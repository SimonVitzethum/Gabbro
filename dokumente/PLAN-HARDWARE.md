# PLAN-HARDWARE — die vier Punkte, die Vertrauensbasis und die Verdrahtung

*Angelegt 2026-09-01 auf `f1831fa`. **Jede Zahl hier ist an diesem Stand gemessen**, und
wo eine fehlt, steht das dabei. Der Plan entstand aus einer Durchsprache der vier
hardwarenahen Punkte — MMIO, DMA, Interrupts, Seitentabellen — und hat unterwegs die
Frage verschoben, um die es eigentlich geht.*

---

## §0 — Zuerst die Definition, sonst ist die Frage unbeantwortbar

„Ohne `unsafe`" kann zwei Dinge heißen, und **nur eines davon ist erreichbar.**

**Nicht erreichbar: keine Vertrauensbasis.** Irgendwo endet jede Kette in einer Aussage,
die niemand aus etwas anderem ableitet — dass dieses Gerät an dieser Adresse liegt, dass
diese Speicherart so ordnet, dass der Prozessor das tut, was das Handbuch sagt. Verve, das
genaueste Ergebnis im Feld, hat einen verifizierten Assembler-Nucleus und einen Beweis, der
ihn mit dem Rest verbindet. **Auch dort ist die Basis nicht null — sie ist klein, benannt
und maschinell geprüft.**

**Erreichbar und der eigentliche Inhalt: kein Konstrukt, das Prüfung abschaltet.** Rusts
`unsafe` ist ein Schalter mit unbegrenztem Umfang. Gabbros `assume … falsifier` ist das
Gegenteil: eine einzelne benannte Aussage mit einem Weg, sie umzuwerfen.

> **Der Unterschied ist nicht Sicherheit gegen Unsicherheit, sondern ZÄHLBAR gegen
> UNZÄHLBAR.**

Der Rest ist Arbeit an einer Zahl: wie viele Annahmen, wie groß jede, **wie viele haben eine
Probe, die auf der Architektur läuft, auf der sie brechen könnte.**

### Der Satz, gegen den dieser Plan gemessen wird

> **„Ohne `unsafe`" ist heute wahr in dem Sinn, dass kein Konstrukt Prüfung abschaltet. Es
> ist noch nicht wahr in dem Sinn, dass die Absenkung nicht raten darf. Der Unterschied ist
> zwölf Wildcards weit, und das ist eine Bahn, keine Forschungsfrage.**

---

## §1 — Die Vertrauensbasis liegt nicht, wo sie vermutet wurde

Bis zum 2026-08-31 wurde die `assume`-Liste als Vertrauensbasis geführt. **Das ist falsch,
und die Messung sagt es:**

```rust
fn breite_von(i: &IntTy) -> u32 {          // emit.rs:3447
    U8|I8 => 1,  U16|I16 => 2,  U32|I32 => 4,
    _ => 8,
}
```

**Unter allen vier Hardwarepunkten liegt diese eine Zeile.** Ein `u128`-Register, ein neuer
Ganzzahltyp — und der Erzeuger schreibt still `volatile uint64_t *` auf ein Gerät. Der
Prüfer sagt `0 errors`, `cc -Werror` ist sauber, das Gerät bekommt einen falsch breiten
Zugriff. **Kein Gabbro-Programm kann sich davor schützen.**

> **Die Vertrauensbasis von Gabbro ist nicht die `assume`-Liste, sondern der Erzeuger** —
> ein paar tausend Zeilen Rust ohne Beweis. **Zwölf Wildcards und sechs Verteilerinstanzen
> sind die gemessene Form davon.**

Daraus folgt die Rangfolge von §6: **Punkt 1 bis 4 im Typsystem zu schließen ändert nichts,
solange die Absenkung raten darf.**

### Die zwölf, gemessen (2026-08-31, `eprintln!` statt `panic!`)

```
emit.rs:3488   148 Treffer   1 Fall    (8, false)      gabbro_setz_le64
emit.rs:3510   107 Treffer   1 Fall    (8, false)      gabbro_le64
emit.rs:2410    26 Treffer   1 Fall    Typ(Bool)
emit.rs:1813    21 Treffer   1 Fall    None
zeugnis.rs:758  18 Treffer   5 FAELLE  ElementeVon KetteIn Schlange SlotsVon Threads
domaene.rs:898   8 Treffer   1 Fall    Wahrheit
emit.rs:3690     4 Treffer   1 Fall    I64
emit.rs:3447     —                     `_ => 8` — liefert eine ZAHL, vom String-Grep nicht gesehen
still: fremdverengung.rs:67 · aufrufgraph.rs:825 · zeremonie.rs:826 · m1.rs:4181
```

> ### BERICHTIGUNG 2026-09-01 — zwei dieser Buchungen waren FALSCH
>
> ```
> breite_von   hier gebucht: SCHWEIGT (0)    nachgemessen: 146 Treffer, nur `U64`
> domaene.rs   hier gebucht: 8               nachgemessen: 2 je Lauf
> ```
>
> **Ausgerechnet die Stelle, die dieser Abschnitt als Wurzel benennt, stand darin als
> schweigend.** Und die `8` kam daher, dass **vier Befehle denselben Pass fahren und die
> Treffer in einen Topf fielen** — *ein Messgerät, das viermal zählt, was einmal geschieht.*
>
> Acht feuern, vier schweigen; die Zeile oben sagte sieben. **Zwei weitere Wildcards
> derselben Klasse fehlten in der Liste ganz:** `umgebung.rs::breite_von` mit
> `_ => (64, false)` — *machte jedes unbekannte Wort vorzeichenlos, die schärfste
> Fehlantwort* — und `emit.rs::ctyp` mit `if f32 {} else { double }`, denn **ein `else` ist
> derselbe Wildcard mit anderer Schreibweise.**
>
> **Erledigt seit `e5e555d`:** `intty` und `breite_von` sind **eine Tafel**
> (`ganzzahlwort`), acht Worte, sonst `C001` an der Spanne. Vier Proben halten sie gegen
> `kw::ALLE` — *ein neuntes Ganzzahlwort ist jetzt eine rote Probe statt eines stillen
> `volatile uint64_t *`.*
>
> **Nicht gestrichen, und das ist ein Urteil:** `_ => None` bleibt. *Ein `_`, der einen
> plausiblen WERT liefert, ist das stille Byte; ein `_ => None` liefert nichts und schiebt
> die Entscheidung an den Rufer.*

**Drei Kategorien, nicht zwei** — und das ist die ehrliche Buchung:

| | |
|---|---|
| **1 echter Befund** | `zeugnis.rs:758` — nicht injektiv, s. §5 |
| **6 prospektive Löcher** | tragende Standardzweige, als `_` geschrieben statt benannt. *Falsch wird erst der siebte Fall* |
| **4 Korpuslücken** | „schweigt über 494 Dateien" ist eine Aussage über den **Korpus**, nicht über die Sprache |

**Kein einziges heute falsch erzeugtes Byte.** Ein gutes Ergebnis und ein langweiliges, und
es gehört so gebucht, damit die Arbeit nicht rückblickend dringender aussieht, als sie war.

> *Ausnahme, gemessen am 2026-09-01: der siebte Fall zu `emit.rs:2410` **wurde
> geschrieben**. `0 errors`, und der Erzeuger schreibt `stufe = 0` (`u32 in 1..9`,
> außerhalb des Typs). **Aus prospektiv wird gemessen.***

### Warum die Reparatur billig ist

**Totalität ist in Rust erzwingbar.** `#![deny(unreachable_patterns)]` hilft nicht, aber
jeden Wildcard über einem sprachnahen Enum zu streichen schon.

> **Danach ist jeder neue Sprachfall ein Übersetzungsfehler statt eines stillen Bytes.**

Für `breite_von` reicht Aufzählen nicht: **eine Breite außerhalb der Aufzählung muss `C001`
sein, kein Vorgabewert.** Der Erzeuger sagt an anderer Stelle schon genau so ab, und der
Text steht da: *„the emitter refuses by name instead of emitting something plausible — a
generator that guesses undoes every pass in front of it."*

**Die Absicherung ist vorhanden und Pflicht:** die Gegenrichtung über alle Korpusdateien
muss nach dem Aufzählen byteweise unverändert sein — `pruefe` **und** das erzeugte C, zwei
Binärprogramme. *Kippt eine Datei, war die Zuordnung geraten.*

---

## §2 — MMIO: am nächsten an fertig, und zwei Löcher

### Was steht

```gabbro
device Virtq(kopf : Pa) at dma {
    reg USED_IDX  : u16 wrapping @0x202 class rw in setup, r in live
    reg AVAIL_IDX : u16 wrapping @0x102 class rw
}
```

```c
uint16_t _v = (*(volatile uint16_t *)(d->basis + 16));
(*(volatile uint16_t *)(d->basis + 16)) = (uint16_t)((_v & (uint16_t)~(uint16_t)240u) | …);
```

Feste Adresse, exakte Breite, `volatile` (120 Vorkommen). Und darüber hinaus:

* **`class rw in setup, r in live`**, getragen von `linear ghost type QueuePhase order { setup, live }`.
  *Ein Register, dessen erlaubte Operationen sich mit dem Protokollzustand ändern, und ein
  Prüfer, der den Zustand mitführt.* Adas Representation Clauses legen Layout und
  Volatilität fest, **die Zugriffsrechte sind dort statisch für die Lebensdauer des
  Objekts.** Aus keiner produktiven Sprache ist mir das bekannt. *Das ist ein schmalerer
  Anspruch als „einzige Sprache mit sicherem Hardwarezugriff" — und er hält.*
* **`u16 wrapping`** — der Umlauf steht an der Deklaration, nicht in der Rechnung.
* **„Ein Register wird EINMAL gelesen"** (`beispiele/44`) — die Bindung trägt die Schranke.

### Geprüft und in Ordnung: `~` trägt die Breite

Alle vier Erzeugerstellen schreiben `({c})~({c})…`. Numerisch nachgerechnet:
`(uint16_t)~(uint16_t)240u` = `0xFF0F`, Ergebnis `0xAB3D` — richtig. **Ohne den äußeren
Cast wäre der Zwischenwert `0xFFFFFF0F`** (Integer Promotion nach `int`), und `-Wall
-Wextra` warnt dort meist nicht. **Die Falle ist real und hier nicht offen.**

*Pikant bleibt: der Erzeuger schreibt `~`, die Sprache kennt es nicht (`L006`). Es gibt
also keine Quellzeile, in der die Breite steht — sie kann nur aus dem Kontext kommen.*

### Was fehlt

- [ ] **Die Absenkung muss total sein** — Breite außerhalb der Aufzählung ist `C001`. §1.
- [ ] **`at port` ist abgesagt, nicht gelöst.** *Eine abgesagte Absenkung ist ein Loch im
      Anspruch, kein geschlossener Punkt.* Solange Portzugriffe außerhalb der Sprache
      stattfinden, gilt „MMIO gelöst" **für memory-mapped und nicht für x86-I/O.**
      *(Der Befund davor war schärfer: `at port` senkte `0x3FD` als Speicheroffset ab — „the
      generated C reads RAM. Not a missing instruction: a different instruction on a
      different thing." Heute benannt abgesagt, `0 device … at port` im Korpus.)*
- [ ] **RMW auf ein Gerät ist drei Erzeugerschritte, und die Atomarität steht nirgends.**
      Bei einem Register, das ein Gerät nebenläufig ändert, ist RMW schlicht falsch. Ein
      `modify`-Konstrukt, das **W1C-Register und geteilte Register unterscheidet**, wäre die
      Fortsetzung derselben Idee wie die Phasenklasse.

---

## §3 — DMA: der Kern ist Sichtbarkeit, nicht Kohärenz

### Was steht

Sechs Adressräume im Typ: `normal 312 · mmio 29 · dma 13 · port 6 · code 2 · boot 1`.
Die Eigentumsübergabe an das Gerät ist **`consumes` plus Phasenklasse** — die lineare Marke
schreitet fort, und der Prüfer weiß, wem das Register gehört.

`device … at dma` **senkt nicht ab** und sagt es unter Namen (`C001`): *„Welche Barriere ein
DMA-Zugriff braucht, ist eine Aussage über das Speichermodell, und der Erzeuger baut sie
nicht — er trägt sie unter ihrem Namen."*

### Der Befund: `dma_kohaerent` ist eine Konjunktion mit EINEM Falsifikator

```gabbro
assume dma_kohaerent
    "Ein Traeger im dma-Raum ist kohaerent: Geraet und Kern sehen dieselben Zellen ohne
     Cache-Pflege, und zwei volatile Zugriffe in Programmreihenfolge werden dem Geraet in
     dieser Reihenfolge sichtbar."
    falsifier sonde_dma_reihenfolge;
```

**Zwei unabhängige Behauptungen unter einem Namen:**

1. **Kohärenz** — Gerät und Kern sehen dieselben Zellen ohne Cache-Pflege.
2. **Ordnung** — zwei volatile Zugriffe werden dem Gerät in Programmreihenfolge sichtbar.

**Die zweite folgt nicht aus der ersten, und beide sind architekturabhängig.** Auf AArch64
gilt die Ordnungsaussage für Device-nGnRnE, aber `volatile` in C11 erzeugt dort **keine
Barriere gegenüber normalem Speicher**: ein Deskriptorschreiben in kohärentem RAM und ein
anschließendes Doorbell-Schreiben ins Gerät können ohne `DSB` in falscher Reihenfolge
sichtbar werden. *Der Deskriptor ist normaler Speicher, das Doorbell ist Device-Speicher,
und genau diese Kombination ordnet ARM nicht.*

**Caprock hat beide Architekturen.** Die Annahme ist für x86 wahr und für AArch64 in der
wichtigsten DMA-Konfiguration falsch — **und ihr Text trägt keinen Architekturparameter.**

```
assume = "assume" ident string …        SYNTAX.md:1476   KEIN `arch`
arch kennen: entry · boot · device      23x x86_64, 2x aarch64
```

> **Ein Falsifikator, der auf x86 grün ist, sagt nichts über den Fall, in dem die Annahme
> tatsächlich bricht.**

### Und die Ordnungshälfte ist gar keine Annahme

Sie ist **ableitbar**. Welche Barriere zwischen einem Schreiben in `normal` und einem
Schreiben in `dma` oder `mmio` nötig ist, folgt aus dem Speichermodell der Architektur und
aus **den beiden Adressräumen, die im Typ schon stehen.** Der Erzeuger hat alle Information,
um `DSB ST` bzw. `sfence` selbst zu setzen.

> **Das wäre der Punkt, an dem Gabbro etwas kann, das keine andere Sprache tut: Barrieren
> aus Adressraumwechseln ABLEITEN statt sie anzunehmen.** Die sechs Räume sind die
> Voraussetzung dafür, und sie existieren schon.

### Aufgaben

- [ ] `assume` bekommt einen `arch`-Parameter, wie `entry` ihn hat.
- [ ] `dma_kohaerent` wird zwei Annahmen, jede mit `arch` qualifiziert.
- [ ] **Zählen, wie viele der übrigen `assume` dieselbe Gestalt haben** — eine Konjunktion
      unter einem Namen mit einem Falsifikator für beide Hälften.
- [ ] Barrieren aus Adressraumwechseln ableiten. **Hängt an `assume … arch`.**

### Was Annahme bleiben muss

Dass ein `dma`-Träger überhaupt kohärent gemappt ist — das entscheidet die Seitentabelle,
also §5. **Der Falsifikator muss auf AArch64 laufen, sonst prüft er den Fall nicht, für den
er da ist.**

### Was nicht modellierbar ist

Dass das Gerät den Puffer **nur im vereinbarten Fenster** berührt. Das ist eine Aussage über
fremde Hardware. *`consumes` plus Phase ist die richtige Kodierung der Absicht, ein Beweis
wird es nie.*

---

## §4 — Interrupts: Vertrag vollständig, Rumpf ist C

```gabbro
entry syscall vector 0x80 arch x86_64 {
    regs in  { nr : rax, a0 : rdi, a1 : rsi, a2 : rdx, a3 : r10, }
    regs out { ret : rax, }
    preserves { rbx, rbp, r12, r13, r14, r15 }
    clobbers  { rcx, r11 }
    stack kernstapel per cpu nested never
    dispatch beispiel::eintritt::syscall_verteiler;
}
```

Registerbelegung, Erhaltung, Zerstörung, **welcher Stapel und ob er verschachteln darf** —
als Typ, nicht als Kommentar. `lock … masks irqs` an 8 Stellen.

**Aber `entry` erzeugt einen Prototypen und einen Vektor, keinen Rumpf.** Solange der
Verteiler außerhalb liegt, sind `preserves` und `clobbers` **Behauptungen über fremden
Code.**

- [ ] **Den Rumpf in Gabbro schreiben.** Möglich und nicht besonders schwer — *der
      schwierige Teil, die Registerkonvention, steht schon im Typ.*
- [ ] **Was ein Handler aufrufen darf.** `nested never` regelt Verschachtelung, aber nicht,
      dass ein Handler keine Sperre nimmt, die ein unterbrochener Pfad hält.
      **Der Rangpass kennt Ränge und `masks irqs`, ihm fehlt nur die Regel** — ein
      `entry`-Rumpf darf keine Sperre nehmen, die IRQs nicht maskiert. *Verdrahtung zwischen
      zwei vorhandenen Teilen, s. §7.*

---

## §5 — Page tables: three layers, and the CHEAPEST one was measured against the wrong thing

*Rewritten 2026-09-01, after the first measurement against an existing SYSTEM instead of
against this tree. Three of the four claims this section stood on moved.*

```gabbro
walk Seitentabelle levels 4 {
    node : [Pte; 512],
    down : rahmen when it.praesent && !it.gross,
    invariant wx_getrennt cost O(n) runs online :
        forall m in mappings of Self : !(m.schreibbar && !m.nx);
}
```

`walk` carries **structure and termination** (4 levels, 512 entries, the descent ends by
construction). The invariant it does not carry — and since 2026-08-31 the emitted C says so
under its own name instead of claiming the opposite:

```c
/* invariant wx_getrennt runs online -- NOT checked here and by no pass either;
 *   it stands as a `W` obligation in `gabbro pflichten`. */
```

- [x] **`runs online` without a generated check.** Closed 2026-08-31, and NOT as `C001`: the
      word `online` names three classes and only one fails. Booked as a `W` obligation
      instead. *A rule over the word would have hit two working registers to reach the one
      that does not work.*

### The register, measured

```
handle:  ./target/debug/gabbro pflichten <file> | grep '^W'
         over beispiele/*.gab + messung/*/*.gab   --   171 files, no gift/

beispiele/07-eintritt-und-boot.gab    wx_getrennt · kein_nutzer_im_kern            2
messung/grammatik/blocklauf.gab       kein_block_im_kopf · geteilt_bleibt_lesbar   2
messung/proben/probe-stellungen.gab   s9_mappings                                  1
```

`instrumente/zaehle-lean.py` books the same five under `walk-invariant`: *"owed by NOBODY."*

### `W29` first: count the uses BEFORE the rule, and ask whether they go wrong the same way

**The five `walk` declarations are not five page tables.**

| what it is | files | levels × width |
|---|---|---|
| an x86_64 page table | `beispiele/07`, `messung/fragmente/F09` | 4 × 512 |
| a filesystem **inode block tree** | `messung/grammatik/blocklauf` | 3 × 256 |
| a domain-position probe | `probe-stellungen`, `probe-neun-domaenen` | 2 × 512 |

> **A rule that fires on `walk` and means "page table" is wrong for three of five** — and
> `blocklauf.gab` was written to catch exactly that: *"If `walk` can only describe page
> tables, it shows up here."* **The distribution is not uniform, and it runs against the
> reading §5 used to assume.**

---

### Layer 1 — TLB · **the construct has a WITNESS, and the rule does not belong at the write**

*The demand cannot be measured on this tree. Measuring it there would be a circle:* a PTE
write without an invalidation construct is not sensibly writable today, so it does not stand
in the corpus, so Rule A refuses, so the construct never comes into being. **The corpus
carries zero statements that write a page-table entry** — 3 of 6 walk-typed places are
writable, one is a declaration without a body and two have empty bodies — *and that number
says nothing about the need.*

**The witness is `../caprock-messbasis` (branch `arch/x86_64`, read-only, never committed
into). Measured 2026-09-01:**

```
handle:  a line that ASSIGNS and whose VALUE is a page-table entry -- a descriptor helper,
         a raw entry OR-ed from the flag constants, or a bare 0 -- plus every
         `write_entry(…)` call in vtd.rs. The handle is the RIGHT-hand side, because the
         target shapes vary: `pd[i] =`, `*e =`, `pt[b].0[i] =`,
         `unsafe { table_mut(p)[i] = … }`, `(*addr_of_mut!(PDPT)).0[g] =`.
         Invalidation distance is counted in CALL FRAMES, not in lines.
denominator: crates/caprock-hal/src/x86_64/{mmu.rs, vtd.rs}, 139 .rs / 75 294 lines in tree

page-table entry writes                                          51
   mmu.rs   (x86_64 page tables)                    37 in 22 functions
            (the 22nd is `adopt_high_ram`, added by hand -- see below)
   vtd.rs   (VT-d root, context and second-level)   14 `write_entry` call sites

by KIND of change, and the classes do NOT go wrong in the same direction:

   CHANGE or REMOVE of a LIVE entry      6 fns   7 writes    invalidate 6 of 6
       protect_page · guard_unmap · guard_remap · guard_block ·
       vspace_unmap_page · vspace_unmap_block
       four in their own frame, two via `vspace_unmap` -> `flush_asid`
   ADD of a new entry                   13 fns  26 writes    3 own · 3 caller · 7 NEVER
   teardown of an unreachable table      3 fns   4 writes    3 via `vspace_teardown`
   the IOMMU half                       14 writes            14 of 14, inside the write
   SWITCH (CR3; writes no entry at all)  set_user_vspace, and `axiom write_cr3` has it
```

*One of the 51 was added by hand:* `adopt_high_ram`:507 splits its assignment across two
lines, and a line-based handle cannot see it. **It is named rather than quietly dropped** —
the number is 51 because a human read the miss, not because the grep said so.

**Every single change to a live mapping invalidates. Six of six, and not one is missing.** A
rule *"a PTE write emits `invlpg`"* would therefore be **redundant where it is right and
wrong where it is not**: it would add an invalidation to twenty-six ADD writes, fourteen of
which deliberately omit it.

> **The rule belongs at the KIND of change, not at the write.** Change or removal of a live
> entry → invalidation, and on several cores a shootdown. Addition → rests on a named
> assumption. Address-space switch → CR3, already carried by `axiom write_cr3`.

**And the architectural half is not a language question.** Whether not-present → present
needs an invalidation is a statement about the machine: Intel's SDM *permits* implementations
to cache not-present entries in the paging-structure caches, and AArch64's safe answer
differs. Caprock states it in prose at `mmu.rs`:379 and acts on it inconsistently — 6 of 13
ADD functions invalidate anyway.

- [x] **Written down as the assumption it is, 2026-09-01**, and it cost no word:
      `beispiele/06-annahmen.gab`, `assume neuer_eintrag_verdraengt_nichts arch x86_64 …
      falsifier sonde_praesent_ohne_invalidierung`. *A lowering that decided this would decide
      it for both architectures at once, and for one of them wrongly.*

**And the sentence that used to launch this layer was measured on the wrong denominator
(`W28`).** It read *"no construct of the language names it; measured, `tlb`/`invlpg`/
`shootdown` occur in no language construct."* True of the **vocabulary**, and read as a
statement about **coverage**. In the corpus the TLB is named four times in two files —
`axiom invlpg(v : u64) effects { writes tlb } falsifier sonde_invlpg` stands in
`beispiele/06`, and `SPRACHE.md`:285 assigns privileged instructions to the axiom layer on
purpose.

#### The success mark, and it is not `unsafe`

`flush_va_global` is one `unsafe { asm!("invlpg …") }`. Counting those is the wrong mark:
**the `unsafe` does not disappear, it moves from the caller's discipline into the lowering.**

*Caprock has already made that move by hand, in the IOMMU half, and says why in its own
words* (`vtd.rs`:1261):

> *"Damit das keine Disziplinfrage bleibt, geht **jeder** Tabellenschreibzugriff durch
> `write_entry`, das nie ohne Flush zurückkehrt."*

`write_entry(addr, v)` is `write_volatile` plus `flush_entry`, and 14 call sites go through
it. **That is the construct of Layer 1, written in Rust, enforced by a comment.** So the mark
is *forgettable sites* — places that could omit the invalidation and still compile:

```
                        forgettable today      under the construct
Caprock MMU  (37 writes)        37                      0
Caprock IOMMU (14 writes)        0  -- by hand           0
```

**The IOMMU column is the whole argument in two numbers.** Someone needed this badly enough
to build it manually for one of two families; the other family is still discipline, and 6 of
6 correct there is a fact about today, not a guarantee.

- [ ] **Not built here, and the reason is ordering, not doubt.** The rule needs the KIND of
      change as a language notion, and `walk` does not distinguish an ADD from a CHANGE
      today. *Building the lowering first would emit the invalidation at
      twenty-six ADD writes, fourteen of which Caprock deliberately leaves bare.*

### Layer 2 — Preservation · **the induction breaks, and it breaks on a reading nobody made**

**W⊕X is not a property of the descent but of the CHANGE.** And the sharpening that was
supposed to halve the cost:

> ~~A single PTE write can violate W⊕X only at the one entry it writes. Carried as an
> INDUCTION, the check needs no quantification over the domain — and `mappings of` drops out
> as a cost problem.~~

**It is false, and the counter-example is the hierarchy.** On x86-64 the effective permission
of a mapping is not the leaf's bit: effective W is the **conjunction** of `RW` over the whole
path, effective X the **negation of the disjunction** of `NX`. So:

> Take a leaf with `RW=1, NX=0` under a PML4 entry with `RW=0`. Effective W is 0 — W⊕X holds.
> **Now write that one PML4 entry, setting `RW=1`. Nothing at the leaf changed.** W⊕X is now
> violated at every executable leaf below it — **up to 512³ = 134 217 728 entries the write
> never touched.**

**And whether that counter-example exists at all depends on a reading this tree has never
made.** `mappings of` is decided as the leaf SET (`SPRACHE.md`:930, bound `node length ^
levels` = 68 719 476 736); what `m.schreibbar` MEANS is not decided anywhere:

| reading of `m.schreibbar` | is it the hardware property? | is the entry-induction sound? |
|---|---|---|
| **the leaf entry's own bit** | **no** — strictly stronger; refuses tables x86 permits | yes, plus a domain-growth side condition |
| **effective (∧/∨ over the path)** | **yes** | **no** — one interior write moves up to 512³ leaves |

> **The two properties Layer 2 needs cannot both hold, and nobody has chosen.** *That is the
> finding, and it is worse than the cost question it was hiding.*

**A second, independent break, and it needs no permission hierarchy at all.** A bound mapping
carries two families of field:

| | | survives a graft? |
|---|---|---|
| fields of the node `format` | `m.schreibbar`, `m.nx`, `m.block` | **yes** — they travel with the entry |
| fields the domain SYNTHESISES | `m.va`, `m.level`, `m.index` | **no** — derived from the PATH |

Grafting a subtree that satisfied `kein_nutzer_im_kern` below `index[0] = 0` under
`index[0] = 256` **re-derives every `va` in it** and breaks the invariant — *without a single
bit changing anywhere in the table.* Over the five corpus invariants:

```
handle:  does the predicate mention `va`, `level` or `index`?

path-INDEPENDENT   4 of 5   wx_getrennt · kein_block_im_kopf ·
                            geteilt_bleibt_lesbar · s9_mappings
path-DEPENDENT     1 of 5   kein_nutzer_im_kern   beispiele/07:34
```

**One of the two invariants §5 quotes.** And until 2026-09-01 no pass could tell them apart,
because no pass read the field names of a bound mapping at all — `forall m in mappings of
Self : !m.gibtsnicht` passed with `0 errors, 0 hints`. That is now `D020`
(`beispiele/gift/570`), and it cost no word.

#### The way out, and it is blocked twice — measured, not assumed

Carrying the induction over **PATHS** instead of entries repairs the hierarchy break: the
check stays local but needs the ancestors' permissions. `ancestors of` exists. It does not
reach here:

```
forall a in ancestors of Self : …   inside a `walk` invariant
  error: [D018] `ancestors of Self` needs a slot of a table, and `Self` is a `walk`
```

1. **`D018` refuses it by kind** — `ancestors of` takes a table or an index into one.
2. **And the bound is silent behind it.** `domaenenschranke` answers `VorfahrenVon` out of a
   table's capacity; a `walk` has no table, so it would return `None` and `K003` would ask for
   a declaration. *The bound is not missing in principle* — an ancestor chain in a `walk` is
   `levels` long and that stands in the declaration — **it is one field nobody reads for this
   purpose.**

> **Do not build across that coupling.** A path induction built before the bound stands
> inherits exactly the cost problem it was meant to dissolve. *And a correction to `§51 S1`
> while this was measured: `domaenenschranke` has **two** callers, not one — `kosten.rs`:665
> and `m1.rs`:3824. This file's own head paragraph has said so since 2026-08-19.*

- [ ] **A `mapping` construct with the `walk` invariant as a postcondition — not built.**
      Ordered behind: (a) deciding what `m.schreibbar` means, (b) `ancestors of` over a
      `walk`, (c) its bound. *Only (c) is arithmetic; (a) is the one that decides whether the
      invariant means what its name says.*

### Layer 3 — Self-reference · **booked as an assumption, and that is more than it looks**

The kernel changes the mapping under which its own code runs. seL4 draws the cut and proves
functional correctness **under the assumption that the kernel stays mapped**.

**Measured over all of Caprock (139 `.rs`, 75 294 lines): no site, no comment, no document
writes down which region must stay unchanged under every change.** *Probably because there is
no form for it* — which makes the sentence below the first of its kind in reach, and for the
same reason **unchecked**: there is no version to hold it against.

What such a statement has to say is three clauses, and only two are expressible:

1. **A REGION, named in the declaration.** `beispiele/07` already writes the negative half
   with no new word: `ensures !exists m in mappings of kern_wurzel : m.rahmen >=
   BOOT_RAHMEN_UNTEN && …`. The self-reference clause is that sentence turned around.
2. **The MOMENT it must hold — and this is the half nothing can say.** A postcondition speaks
   about the state after a body; the kernel's own mapping must survive **every intermediate
   state**, because an interrupt can arrive between two entry writes. *That is a statement
   about a TRACE*, and `§51 S2` books the same wall for frame conditions.
3. **Which region counts as "the kernel's own" — and the construct must not guess.** `.boot`
   is a link-time stretch and not a bit in the entry; `beispiele/07` passes
   `BOOT_RAHMEN_UNTEN`/`_OBEN` in from the linker, and a self-reference clause takes the same
   road.

- [x] **Booked as an `assume` and not as an `invariant`, 2026-09-01**, because of clause 2:
      `assume kern_bleibt_unter_jeder_aenderung_abgebildet … falsifier sonde_kern_entmappt`.
      **An assumption no probe could contradict would not be a statement** (`N031`); this one
      has a concrete probe — *unmap the region artificially and see whether the system falls.*
- [ ] **Do not build a construct.** Two of three clauses would look complete while the third
      is the one seL4 also only assumes. *A construct that hides that is worse than an
      assumption that names it.*

---

## §6 — Und das Zeugnis ist die zweite Hälfte der Absenkungsfrage

Das Zeugnis soll belegen, **dass das C das Programm ist**. Gemessen am 2026-08-31:

```
traverse t over threads  by unvisited …     6 items, 0 errors, 0 hints
traverse t over queue r  by unvisited …     6 items, 0 errors, 0 hints
                                            Quellen: EINE Zeile Unterschied

gabbro zeugnis  ->  md5 152d61a6…  BEIDE MALE
                    table.induktion   proved   1x  traverse
```

`zeugnis.rs:758` führt `ElementeVon`, `KetteIn`, `Schlange`, `SlotsVon` und `Threads` auf
einem `_ => "traverse"` zusammen.

> **Ein Zeugnis, das zwei verschiedene Programme belegt, belegt keines von beiden.**

Und der Grund, warum das mehr ist als Kosmetik:

> **Ein Zeugnis, das injektiv ist, wäre die eigentliche Absicherung gegen Erzeugerfehler,
> weil es nicht vom Erzeuger abhängt.**

Das Paar liegt als `messung/proben/probe-zeugnis-injektiv-{a,b}.gab` im Baum. Die Heilung
ist **nicht gebaut** — welchen Ausweis jede der fünf Formen bekommen soll, folgt erst aus
dieser Messung.

- [x] **Injektivität gebaut, `e5e555d`** — das Paar gibt jetzt `30a2f4b0…` gegen
      `8e040dca…`, und die Antwort folgte aus der Messung: **nicht neun Etiketten, sondern
      neun GRÜNDE.** Dabei fiel auf, dass **drei Domänen auf gar keiner Schranke ruhen**
      (`chain(…) in`, `fields of`, `threads`). `tests/zeugnis_injektiv.rs` misst beide
      Richtungen unter demselben Dateinamen, falsifiziert und zurückgestellt.
      *Offen bleibt: injektiv in den TRAVERSIERUNGSDOMÄNEN, nicht allgemein — 36 Paare.*
- [ ] ~~Injektivität bauen, und die Probe so, dass sie es **misst statt behauptet**~~: das Paar
      muss danach verschiedene Zeugnisse haben, und die Gegenrichtung — zwei gleiche
      Programme geben gleiche Zeugnisse — gehört daneben.

---

## §7 — Das Bauprofil: sechs Instanzen, und es ist ein Prozessbefund

Am 2026-08-31/09-01 ist **sechsmal dieselbe Form** an unabhängigen Stellen gefallen:

| Teil A | Teil B | was fehlte |
|---|---|---|
| `linear ghost` (Griff) | `27-freiliste.gab` | der Zeuge existiert, die Freiliste führt ihn nicht |
| `boot` | `backed` | `bss_nullen(0x2000,0x3000)` = 4 KiB, größtes Feld 16 MiB |
| Prüfer | Erzeuger | `match g { Griff(i) => … }` prüft grün, `C001` beim Erzeuger |
| `gabbro lean` | `umgebung::kandidaten` | `lean` **klebt Text**; der Resolver folgte `use` längst |
| `m2::endet` | `crate::endet_immer` | ein **viertes** Register derselben Dreierliste, andere Semantik |
| `breite_von` | zwei Verteiler | eine Wurzel, zwei Wege, keiner kennt den anderen |

> **Die Teile entstehen einzeln und korrekt, die Verdrahtung entsteht nie — weil sie zu
> keinem Konstrukt gehört und deshalb in keiner Bahn steht.**

**Vier Instanzen sind keine Anekdote mehr, sondern ein Bauprofil.** Die Konsequenz ist
prozessual: **eine Bahn, deren einziger Inhalt „welche zwei vorhandenen Teile wissen nichts
voneinander" ist**, mit derselben Vorabmessung wie jede andere — wie viele Stellen, wie
viele fielen heute. Die sechs oben sind der Startkorpus; **die Zählung sagt, ob es acht sind
oder fünfzig.**

Kandidatenformen für den Zähler, jede mit Begründung:

* **zwei Register über derselben Menge** (W7) — `Return|Leave|Next` steht viermal im Baum.
  *Und die schärfere Frage vor dem Zusammenziehen ist, ob sie dasselbe sagen SOLLEN.*
* **ein Konstrukt beschreibt, ein zweites müsste erhalten** — `walk` gegen PTE-Schreiben,
  `backed` gegen `boot`.
* **Prüfer nimmt an, Erzeuger sagt `C001`** — die vier offenen `H`-Pflichten.
* **ein Angebot, das keine Pflicht ist** — `linear ghost` existiert, zwei Tabellen mit `ops`
  führen es nicht.

---

## §8 — Die Rangfolge, und sie ist nicht knapp

| # | Was | Warum hier |
|---|---|---|
| **1** | **`breite_von` und die zwölf Wildcards** | **liegt unter allen vier Punkten**, und eine Reparatur dort trägt jede spätere Sprachregel. Keine Forschungsfrage. |
| **2** | **TLB / `mapping`** | billig, **real ausnutzbar**, kein Beweisanteil |
| **3** | **Barrieren aus Adressräumen** | die Aussage, **die Gabbro von anderen Sprachen abhebt**. Hängt an `assume … arch` |
| **4** | Sperrregel für `entry`-Rümpfe · `assume … arch` | Verdrahtung, beides vorhanden |
| **5** | Zeugnis injektiv | Absicherung gegen Erzeugerfehler, **unabhängig vom Erzeuger** |
| **6** | Erhaltungsregel (Schicht 2) | Forschungsanteil, aber durch die Induktionsfassung halbiert |
| **7** | Selbstbezug (Schicht 3) | ungelöst, auch bei seL4 |

---

## §9 — Was außerhalb der Sprache bleibt, und das gehört benannt

**Caprocks geteilter Speicher über Capabilities.** Wenn zwei Prozesse dieselbe Seite
schreibbar haben, sagt Linearität nichts — **und kein Konstrukt kann das ändern, weil die
Bedingung stimmt.**

> Der Schnitt ist derselbe wie bei seL4: **geteilter Nutzerspeicher ist außerhalb** — und
> das gehört benannt statt implizit gelassen.

- [ ] Eine Zeile in `BEWEIS.md`, die den Schnitt zieht. *Keine Bahn, eine Zeile.*

Ebenso außerhalb, aus §3: dass das Gerät den DMA-Puffer nur im vereinbarten Fenster berührt.

---

## §10 — Was dieser Plan NICHT ist

Er ersetzt weder `PLAN-VOLLSTAENDIGKEIT.md` (senkt jedes angenommene Programm ab?) noch
`PLAN-VERIFIKATION.md` (was ist bewiesen?). **Er beantwortet eine dritte Frage: wie weit
trägt der Anspruch am Blech**, und wo endet er in einer Annahme statt in einem Beweis.

Und er verpflichtet zu nichts, was nicht gemessen ist. **Jeder Punkt oben mit einem
Kästchen hat entweder eine Zahl daneben oder den Satz, dass sie fehlt.**

---

# TEIL II — Der Wortschatz, und warum er die Beweiskostenkurve ist

*Angefügt 2026-09-01. Derselbe Plan, weil dieselbe Frage: **wo endet der Anspruch in einer
Annahme statt in einem Beweis** — nur diesmal an der Sprache statt am Blech.*

## §11 — Ein Wort ist eine erzeugte Form, und jede erzeugte Form braucht einen Satz

```
Wortschatz (kw.rs)   ~~234~~ 222 Woerter      C: 32      Ada: 70
Absenkungssaetze     Absenkung_Parametrisch.thy deckt EINE (`ops relabel`)
```

> **Die 234 war falsch, und der Irrtum ist reproduziert** (2026-09-01,
> `instrumente/zaehle-wortschatz.py`): ein naiver `grep` über die **Datei** zählt 15 Wörter
> aus Kommentaren mit und verliert `None`, `Self`, `Some`. Die Grundgesamtheit ist der
> Makroaufruf `wortschatz! { … }`; nachgezählt sind es **222** (213 reserviert, 9
> kontextuell), davon **221 im Korpus benutzt** und **eines nur reserviert** (`masked`).

> **Die Beweislast wächst mit dem WORTSCHATZ, nicht mit der Programmgröße.**

Und sie wächst, weil **Totalität mit Vokabular bezahlt wird**: jede neue Rekursionsform
braucht ein neues Konstrukt statt eines Terminierungsbeweises. Das ist der Handel, den
Gabbro überall macht, und er ist bisher nirgends **beziffert**.

- [x] ~~**Eine Ratsche auf den Wortschatz**~~ — **gebaut** (2026-09-01,
      `instrumente/zaehle-wortschatz.py`). *Ein neues Wort nennt entweder das Wort, das es
      ablöst, oder die Messung, warum keine vorhandene Form es trägt* — **zwei Marken**, weil
      die Regel zwei Hälften hat: `MARKE_WOERTER = 222` und `MARKE_OHNE_GRUND = 210`. Ein
      Tausch lässt beide stehen, ein Zuwachs hebt die erste, ein Zuwachs ohne Grund am
      Eintrag beide.
      **Und was sie nicht fängt, steht als Zahl daneben:** 333 Stellungen (Terminal ×
      EBNF-Regel) auf 223 Terminale, 1,49 je Terminal. *Ein Wort, das ein anderes still
      weiter macht, wächst nicht in der ersten Zahl* — `invariant` ging am 2026-08-28 von der
      `table` an alle drei Schleifenformen, und `SYNTAX.md` sagt selbst *„It is not a new
      word."* **Die Stellungszahl ist keine Ratsche und soll steigen:** fällt die erste, ohne
      dass die zweite steigt, wurde Ausdruck verloren statt getauscht.

### Ein Kandidat stand in der eigenen Tafel — und er ist GEFALLEN

`by decreasing e` — *„the same walk. The measure is a witness and says nothing about the run
that `unvisited` does not."*

**Es war ein Beweiszeuge, kein Laufmodus.** Als dritter Modus neben `unvisited`/`consuming`
stand es in der falschen Zone; es gehört zu den **Verträgen**, nicht zum Ablauf.
*Drei Modi, zwei Läufe.*

> **Ausgeführt am 2026-09-01, als erster Fall der Ratsche von §11.** Die Grammatik lautet
> jetzt `"by" ( "unvisited" | "consuming" ) [ "decreases" expr ]`, und `decreasing` ist aus
> `kw.rs` verschwunden: **222 → 221 Wörter, null neue.** Gemessen wurde vorher genau die
> Frage, die dieser Abschnitt stellt — *spart die Verschiebung ein Wort oder verschiebt sie
> nur eines?* Sie spart: das Wort, das den Zeugen jetzt trägt, ist `decreases`, und das stand
> seit «K5.4» am `fn`-Kopf für dasselbe Maß über der Rekursion.
>
> *Dieselbe Bewegung, dieselbe Produktion, drei Tage früher:* `invariant` ging von der
> `table` an alle drei Schleifenformen, und `SYNTAX.md` sagt dazu *„It is not a new word."*
>
> **Und die Ausschließlichkeit fiel mit:** `by consuming decreases e` ist schreibbar und war
> es nicht. **Die Stellungszahl blieb dabei bei 333** — `decreasing` hatte eine Stellung,
> `decreases` hat jetzt zwei statt einer (`fndecl` **und** `traverse`). Die Summe steht, der
> Nenner fiel um eins, und 1,49 wurde 1,50 je Terminal. *Das ist die Gestalt, in der so ein
> Handel einer ist: die Reichweite bleibt, der Wortschatz wird kleiner.* Wäre die Summe
> mitgefallen, wäre Ausdruck verschwunden statt getauscht — und `zaehle-wortschatz.py` druckt
> beide Zahlen nebeneinander, damit man das eine vom anderen unterscheiden kann.
>
> Der Preis, vollständig: 3 Dateien in `gabbro-syntax` · **4 Lesestellen in `gabbro-check`**
> (`lib.rs`, `schleifen.rs`, `zeremonie.rs`, `emit.rs`) · 11 Korpusstellen in 11 Dateien ·
> 9 Teststellen · 2 Grammatikblöcke. `cargo test --no-fail-fast` 15 Sammlungen grün,
> `pruefe-emission.sh` `ALL PASS`, alle vier Giftproben mit unveränderter Kennung.

---

## §12 — Domänen sind der größte Einzelposten

```
ancestors of · chain · child · descendants of · elems of · levels · mappings of
observed · occupied · parent · queue · reaches · sibling · slots of · threads · tree
```

**Siebzehn Wörter**, und *user-defined quantifier domains* existieren ausdrücklich nicht.
Deshalb braucht **jede neue Datenstruktur ein neues Domänenwort.**

> **Es ist kein Zufall, dass `zeugnis.rs:758` als einzige Stelle fünf Fälle hatte:**
> `ElementeVon`, `KetteIn`, `Schlange`, `SlotsVon`, `Threads` sind genau diese Liste.
> §6 und §12 sind dieselbe Sache von zwei Seiten.

**Der Vorschlag ist nicht, benutzerdefinierte Domänen freizugeben** — das öffnet die
Terminierungsfrage wieder. Sondern:

- [ ] **Eine Domäne als deklarierte Erreichbarkeit über einem Tabellenfeld, mit
      Wohlfundiertheitsnachweis an der Deklaration.** ~~*Ein Wort statt siebzehn, ein
      parametrischer Absenkungssatz statt siebzehn einzelner.*~~

> **Gerechnet am 2026-09-01 gegen die Ratsche von §11** (`messung/DOMAENENREGEL.md`). Der
> Posten steht; jede seiner vier Zahlen ist zu groß.
>
> * **Die siebzehn sind keine Messung.** Die Produktion `domain` nennt **elf** Terminale; die
>   Liste oben enthält acht, die nicht darin stehen (`child`, `parent`, `sibling`, `tree`,
>   `observed`, `occupied`, `reaches`, `levels`), und verliert zwei, die darin stehen
>   (`fields`, `in`). `of` und `in` können ohnehin nicht fallen — `in` steht in neun Regeln.
> * **Nur VIER der neun Formen sind Erreichbarkeit über einem Tabellenfeld.** `slots of` und
>   `elems of` sind Indexbereiche (53 der 113 Korpusstellen), `fields of` eine statische
>   Liste, `threads` eine Aussage über die Maschine. Die Regel erreicht **35 %** der Stellen.
> * **`tree`/`parent`/`child`/`sibling` können nicht fallen:** `opsruf.rs`:244 und
>   `emit.rs`:2488/2613 lesen die Kante für den `relabel`-Erzeuger, und
>   `Absenkung_Parametrisch.thy` beweist darüber. *«B41b» hat sie 2026-08-20 ausdrücklich zur
>   STRUKTUR erklärt, nicht zum Durchlauf.*
> * **Es gibt keine siebzehn Absenkungssätze abzulösen — es gibt EINEN im ganzen Baum**, und
>   der handelt von `ops relabel`. Die Bewegung ist **0 → 1**: die Regel *ermöglicht*
>   Beweisarbeit, sie spart keine. Das ist die bessere Begründung, nicht die schwächere.
> * **`zeugnis.rs:758` gibt es nicht mehr** — seit `e5e555d` neun einzelne Zweige und neun
>   Begründungen. §6 ist eingelöst; was bleibt, ist die andere Hälfte.
>
> **Der Fund, der den Posten trägt:** `reach = place "reaches" place "via" ident` steht seit
> jeher in der Grammatik (:709), `reaches` und `via` sind Wortschatzwörter, und
> `beispiele/47`:194 begründet selbst, warum dort `reaches` und nicht `ancestors of` steht.
> **Die Regel ist eine vorhandene Form, aus der Prädikat- in die Domänenseite gehoben** — ein
> Alternativzweig, **null neue Wörter**, drei abgelöste (221 → 218), Stellungen 333 → 332 auf
> 219 Terminale, also **1,50 → 1,52 je Terminal**.
>
> **Und die Rechtfertigung ist die Schranke, nicht der Wortschatz.** `domaenenschranke` hat
> genau EINEN Aufrufer: `kosten.rs`:665. *Ohne `costs`-Zeile fragt niemand nach der Schranke
> einer Domäne* — `domaene.rs` sagt es an einer anderen Domäne selbst: „der Fall stand nie
> auf … also fragte der Kostenpass nie." Ein Nachweis an der Deklaration verlegt die Schranke
> von *„wird gefragt"* nach *„steht fest"*, und das erreicht jede Funktion ohne `costs`.
>
> **Nicht gebaut, Regel A und die Bahngrenze:** 41 Korpusstellen in 23 Dateien, fünf
> Prüferdateien und der ERZEUGER. *Der `decreasing`-Fall desselben Tages war 11 Korpusstellen
> und 4 Prüferstellen; dieser ist das Vierfache.*

Das ist **dieselbe Bewegung, die `Absenkung_Parametrisch.thy` an der Zielsemantik macht,
nur an der Domänenseite — und sie hat dort schon funktioniert.**

**Nebeneffekt:** `mappings of` bekommt seine Schranke aus derselben Regel statt aus dem
Kostenpass. Damit fällt der offene Kostenbefund aus §5 auch von dieser Seite.

---

## §13 — Die Lemma-Decke jetzt entscheiden, nicht bei Caprock

*„hand-written lemmas"* existieren nicht. **Das ist die riskanteste Entwurfsentscheidung im
Dokumentensatz, weil sie erst bricht, wenn der Korpus groß ist — also spät und teuer.**
Das offene Item sagt es selbst: *ein einziger Fall in der letzten Spalte setzt die Decke
tiefer.*

Die Fluchttür existiert praktisch schon (Kanal A, `pflichten --lean`), **steht aber nicht
als Entwurfsaussage da.**

- [ ] Sie ausschreiben: **keine Lemmata in der Quelle; Pflichten verlassen die Sprache
      BENANNT und werden außerhalb erledigt.** Dann ist die Regel wahr und zugleich keine
      Ausdrucksdecke — **und die 67 abgesagten Pflichten sind eine Reichweitenzahl statt
      einer Niederlage.**

---

## §14 — Keine Parametrizität: gemessen, und die Frage ist erledigt

Cogent hat genau hier verloren — die Sprache blieb sauber, **die Duplikation wanderte in den
Korpus und von dort ins handgeschriebene C.** Die Frage ist also nicht ob, sondern wie viel.

**Gemessen 2026-09-01 über die 77 echten Programmdateien** (ohne `gift/`, `proben/`,
`grammatik/`), `table`/`format` mit mindestens zwei Feldern, Skelett = Folge der Feldnamen:

```
68 Deklarationen        62 verschiedene Skelette
davon MEHRFACH: 5       ('belegt','wert') 3x · Pte 2x · ('benutzt','zaehler') 2x
                        ('kopf','naechst') 2x · FaultRecordHi 2x
```

**Die Duplikation ist klein, und die Mehrfachen sind überwiegend dasselbe Lehrbeispiel in
zwei Dateien.** Ohne die Filter sieht es dramatisch aus — 226 Deklarationen, 34 mehrfache
Skelette, `table { wert }` fünfzehnmal — aber das sind Giftproben und Minimalfälle.
*Der Nenner entscheidet die Antwort, nicht der Zähler (W25).*

> **Monomorphie ist damit richtig, und die Frage ist erledigt** — bis der Korpus wächst.
> Die Messung gehört wiederholt, wenn Caprock ganz übersetzt ist.

---

## §15 — Vier kleine, konkrete

### `w1c` und `rc` stehen unter *Typen* und gehören zu *class*

**Ein Write-1-to-Clear-Register ist keine Zahl mit anderem Typ, sondern ein
Zugriffsverhalten.** Es gehört neben `rw`/`r`.

> **Solange es ein Typ ist, ist ein Read-Modify-Write darauf typkorrekt und falsch — und
> der RMW-Erzeuger baut ihn.**

Das ist die zweite Hälfte des offenen `modify`-Punkts aus §2.

### `progress` und `assume` sind dieselbe Sache in zwei Listen

`forever … progress timer_tick_arrives` ist **eine Umgebungsannahme mit Falsifikator** — und
sie gehört in dieselbe zählbare Liste wie `assume`.

> Sonst hat die Vertrauensbasis **zwei Register über derselben Sache.** Dieselbe Form wie
> W7, und dieselbe wie die vier Register von `Return|Leave|Next` in §7.

### `assume` braucht `arch`

Aus dem AArch64-Grund in §3. **Derselbe Posten, hier nur ein zweites Mal getroffen** — was
für ihn spricht.

### E3 gilt für Programme, nicht für den Übersetzer

Die Sprache hat `exhaustive` als Quellwort und **verbietet Auffangzweige** — und der
Erzeuger hatte zwölf.

> **Das ist keine Ironie, sondern eine Regel, die man anwenden kann: `forbid(unsafe_code)`
> hat ein Geschwister, und es heißt „kein `_` über einem Sprach-Enum".**

- [ ] Nach der Aufzählbahn (§1) als **Lint durchsetzbar** — und dann gilt E3 auch für die
      Werkzeugkette, die E3 durchsetzt.

---

## §16 — Was Teil II an der Rangfolge ändert

Nichts an Platz 1: `breite_von` bleibt unter allem. **Aber §15 letzter Punkt hängt daran** —
die Aufzählbahn macht den Lint erst möglich, und der Lint ist es, der die Reparatur
*dauerhaft* macht statt einmalig.

Neu einzureihen:

| # | Was | Warum dort |
|---|---|---|
| **3a** | **`w1c` von *Typen* nach *class*** | billig, und ein RMW auf W1C ist heute **typkorrekt und falsch** |
| **3b** | `progress` in die `assume`-Liste | ein Register statt zwei, W7 |
| **5a** | **Die Domänenregel** (§12) | löst §6, §12 und die `mappings of`-Schranke aus §5 **auf einmal** |
| **6a** | Wortschatzratsche (§11) | die fehlende Zahl; billig, aber ohne sie wächst der Rest unbemerkt |
| **6b** | Lemma-Decke ausschreiben (§13) | **kostet nichts und verhindert eine späte, teure Entdeckung** |

Und die Messung aus §14 ist **abgeschlossen**: keine Bahn, kein Kästchen, ein Ergebnis.

---

# TEIL III — Gegen SPARK/Ada gehalten

*Angefügt 2026-09-01. **Der Vergleich ist die einzige Weise, die Wette zu beziffern** — und
er liefert vier Anleihen, von denen eine groß ist.*

## §17 — Der Unterschied auf drei Achsen

### Beweisen gegen Unschreibbarmachen

SPARK ist **Allzwecksprache plus Verträge plus SMT-Beweiser**: du schreibst die Eigenschaft
hin, das Werkzeug erledigt sie. Gabbro macht die Eigenschaft zur **Grammatikeigenschaft** —
ein Versatz ohne Länge ist nicht formulierbar.

> **Das sind verschiedene Versagensarten.** Bei SPARK bleibt eine Pflicht **unerledigt und
> du siehst sie**. Bei Gabbro ist die Eigenschaft **unausdrückbar und du verlässt die
> Sprache**: `extern`, `iasm`, `assume`.

### Kosten pro Programm gegen Kosten pro Konstrukt — die eigentliche Wette

SPARK zahlt die Spezifikationslast **in jedem Programm neu**; Gabbro zahlt sie **einmal im
Sprachentwurf**. Aber sie verschwindet nicht:

> **Der Wortschatz IST die amortisierte Spezifikation.** Die Wette geht auf, wenn viele
> Programme wenige Konstrukte benutzen, und sie geht schlecht aus, wenn jedes neue Problem
> ein neues Wort braucht.

Das ist §11 von Ada aus gesehen — **und es ist die Zahl, an der man die beiden Ansätze
tatsächlich vergleichen kann.**

### Absage gegen Abstufung

Ada hat einen **Abstiegspfad**: was SPARK nicht beweist, bleibt eine Laufzeitprüfung und
wird zu `Constraint_Error`. Gabbro kennt das nicht — **entweder die Sprache trägt es oder du
bist draußen.**

> Das ist strenger und **praktisch riskanter**, weil der Ausstieg ins Unverifizierte führt
> statt in eine schwächere, aber noch sichere Form.

Dazu die Asymmetrie aus §1: **Adas Zusage gilt für die Quelle, und GNAT ist qualifiziert.
Gabbros Zusage muss durch den eigenen Erzeuger** — also steht er in der Vertrauensbasis.

---

## §18 — Vier Anleihen, und die erste ist groß

### `Depends` — Informationsfluss statt nur Rahmen

**Die wertvollste Anleihe, und die, die `effects` nicht hat.**

```
effects { reads A, writes B }     sagt WAS BERUEHRT WIRD
Depends => (B => A)               sagt WELCHE AUSGABE VON WELCHER EINGABE ABHAENGT
```

Der Unterschied ist genau der zwischen *„diese Funktion liest den Cap-Space"* und *„dieses
Ergebnis hängt von diesem Slot ab"*.

> **Für einen Capability-Kern ist das nicht Kosmetik.** Nichtinterferenz zwischen Domänen
> ist die Eigenschaft, die Caprock eigentlich beweisen will, und **seL4 brauchte dafür eine
> eigene, große Beweisarbeit oben auf der funktionalen Korrektheit.** Aus Flusskontrakten
> fällt eine schwächere Version davon fast umsonst ab.

- [ ] **Und die Erweiterung ist klein, weil `effects` die Namen schon führt — es kommt ein
      Pfeil dazu.**

### Abgeleitete Typen — und diese Fehlerklasse ist bezahlt

`type Portnummer is new u16` — gleiche Darstellung, **nicht mischbar**.

> **Der `at port`-Fehler war exakt das:** eine Portnummer als Speicherversatz gegeben,
> `0x3FD` auf einen Zeiger addiert.

`index into T` macht das für Tabellen schon; **für Skalare gibt es nichts.** Physische gegen
virtuelle Adresse, Slot-Index gegen Objekt-Index, Zyklen gegen Nanosekunden — alles `u64`
und alles verwechselbar.

- [ ] Billig, **erasure-frei**, und trifft eine Fehlerklasse, die der Baum bereits bezahlt hat.

### Der Abstiegspfad, in Gabbros Form

**Nicht Adas Laufzeitausnahme übernehmen, sondern das Prinzip:** eine Pflicht, die statisch
nicht fällt, wird eine **benannte Laufzeitabsage** statt eines Übersetzungsfehlers oder einer
`assume`. `check` und die Absage-Disziplin sind der Baukasten dafür.

> **Der Gewinn ist, dass der Ausstieg IN DER SPRACHE bleibt und zählbar ist, statt in
> `extern` zu führen.**

### Benannte Beschränkungsprofile

`pragma Restrictions` und Ravenscar sind die Idee, dass **eine Teilmenge einen NAMEN hat**
und ein Programm erklärt, in welcher es liegt.

- [ ] Ein Kernmodul erklärt sein Profil, **und das Zeugnis trägt es** (§6).

---

## §19 — Was NICHT übernommen wird

Adas Sichtbarkeitsregeln, `private`-Teile, Vererbung, Generics in Ada-Form — *das ist die
Komplexität, wegen der niemand die Sprache im Kopf hat.* Und §14 hat gemessen, dass
Parametrizität hier kein Bedarf ist.

Und eine Stelle, an der **Gabbro besser ist und die als solche geführt gehört**:

> `pragma Assume` ist **schwächer** als `assume … falsifier`. **Eine Annahme ohne benannte
> Probe ist eine Annahme, die nie umfällt.**

---

## §20 — Der Test, der beide Ansätze vergleichbar macht

Er steht aus, und er ist präzise formulierbar:

> **Eine Caprock-Struktur in beiden Sprachen, und gezählt wird nicht „geht es", sondern die
> ZEILEN SPEZIFIKATION JE ZEILE ERZEUGNIS.**

Der Eichpunkt ist seL4s **20:1**. SPARK gegen diese Zahl, Gabbro gegen dieselbe.

| Ergebnis | was es heißt |
|---|---|
| Gabbro 3:1, SPARK 12:1 | **die Wette ist belegt** |
| beide bei ~10:1 | eine schönere Sprache **und kein Kostenargument** |

> **Und das zweite wäre ein BEFUND, kein Scheitern.** Es steht hier, damit es beim Messen
> nicht nachträglich zum Scheitern umgedeutet wird — dieselbe Disziplin wie bei jeder
> anderen Zahl in diesem Baum.

- [ ] Struktur wählen, beide schreiben, zählen. **Vor dem Schreiben festlegen, was als
      „Spezifikationszeile" zählt** — sonst entscheidet die Definition das Ergebnis (W25).

---

# TEIL IV — Diktat gegen Zusage

*Angefügt 2026-09-01, und dieser Teil **ersetzt §20**. Das Verhältnis Spezifikation zu
Erzeugnis misst die Programmgröße mit — **Logik kann einfach sein und das Programm riesig,
dann ist es 0,0:1; oder andersherum, dann ist es 2:1.** Beides sagt nichts. Die Marke
darunter hängt an keiner Größe.*

## §21 — Das Ziel, als Zahl

> **Ein Nutzer muss nur noch seine eigene Logik beweisen, sonst nichts.**

Der Baum misst schon etwas Ähnliches — `gabbro ceremony` teilt in **ableitbar / redundant /
tragend**. Aber das ist eine andere Frage:

| | |
|---|---|
| **die Tafel fragt** | *darf die Klausel wegfallen?* |
| **das Ziel fragt** | *ist es die eigene Logik des Nutzers?* |

**Ableitbar und weglassbar sind zwei verschiedene Dinge, und die Tafel kennt nur das
zweite.** Dieselbe W16-Gestalt wie überall in diesem Baum: ein Messgerät, das etwas anderes
misst als seinen Gegenstand — nur diesmal nicht als Fehler, sondern als **ungestellte
Frage**.

### Die zwanzig Regeln, neu sortiert nach WESSEN AUSSAGE

*Gemessen 2026-09-01 über 64 Dateien, 1054 Stellen:*

```
  EIGENE LOGIK        188   18 %
     T3     82   requires/ensures -- der Vertrag
     T6     65   Terminierung: Schranke, on_exceeded, progress, decreases
     T12    26   Bereich am Typ
     T5      9   table invariant          T4   6   maintains

  DIE HARDWARE         93    9 %
     T10    35   Registerklasse           T11  35   assume + Falsifikator
     T9     23   reserved-Feld

  BUCHFUEHRUNG        705   67 %
     T1    462   Wirkungseintrag
     T2    211   costs
     T7     25   touches                  T8    7   let-Annotation

  ABLEITBAR, offen     68    6 %
```

> **Zwei Drittel von dem, was ein Gabbro-Programmierer schreibt, ist Buchführung.** Nicht
> seine Logik, nicht das Handbuch — Bücher, die er dem Übersetzer führt.

**Die Marke: `705 → 0` bei bleibenden `188`.** Sie hängt an keiner Programmgröße — *die
Buchführung skaliert mit dem Code, die Logik mit dem Problem.*

> **Die `462` unter T1 ist seit dem 2026-09-01 nachgerechnet und hält nicht.** Über
> `beispiele/*.gab` stehen **439** `effects`-Einträge an einer Funktionsdeklaration, davon
> **359 an einer Funktion mit Rumpf** und **80 an `extern`/`prim`** — und die 80 sind
> Vertrauensfläche, die nicht auf null gehen kann. Ein Textzähler findet **538** Einträge
> überhaupt. *Welche 64 Dateien und welche Träger die 462 meinten, steht nirgends.* **§38.**

---

## §22 — Und beide großen Posten rechnet der Übersetzer schon selbst

```
$ gabbro costs 19-traversierung.gab
-- site           computed  promised  slack
aktive_loeschen         48        64        16

$ gabbro pruefe eff.gab
error: [E005] `f` writes `t.slots[…].a` but declares `pure`
```

**Er weiß die Zahl. Er weiß den Ort.** Er verlangt sie trotzdem vom Nutzer und **prüft dann
nur, ob dessen Abschrift stimmt.**

> **Das ist keine Beweislast, das ist ein Diktat.**

Und der Handel bei der Heilung ist bei beiden derselbe:

* **`costs`** — der Übersetzer schreibt die gemessene Zahl. Der Nutzer schreibt eine Zusage
  nur dort, wo er sie **enger** haben will als das Ergebnis.
* **`effects`** — abgeleitet statt deklariert, mit derselben Ausnahme: wer eine Funktion
  **auf** `pure` festnageln will, schreibt es hin.

> **Beides ändert die Bedeutung der Klausel von „ich habe abgeschrieben" zu „ich
> verspreche".** Das ist kein Verlust an Strenge, sondern das Gegenteil: **eine Zusage, die
> jemand freiwillig schreibt, trägt etwas. Eine, die er schreiben MUSS, trägt nur seine
> Sorgfalt beim Abschreiben.**

---

## §23 — Die Messung vor der Bahn, und sie ist eindeutig

`gabbro costs` über den ganzen Korpus, die `slack`-Spalte histogrammiert:

```
  682 Zusagen mit gerechneter Zahl

  slack == 0     67   (10 %)   exakt abgeschrieben ODER echtes Versprechen
  slack  > 0    594   (87 %)   POLSTERUNG

  Polsterung relativ zur Zusage:      bis 10 %    10
                                      bis 25 %    57
                                      bis 50 %   130
                                      ueber 50 % 397
```

Die großzügigsten mit echtem Rumpf:

```
  ohne_verbrauch      gerechnet    64   zugesagt 100000   Polster 99,9 %
  hoechster           gerechnet     1   zugesagt    512   Polster 99,8 %
  zaehler_erhoehen    gerechnet     6   zugesagt   2048   Polster 99,7 %
```

> **87 % aller Kostenzusagen sind gepolstert, und zwei Drittel davon um mehr als die
> Hälfte.** Eine Zusage mit 99,8 % Polster trägt nichts — sie ist eine gerundete Abschrift.

**Damit steht die These als Zahl statt als Argument**, vor der ersten Zeile Bahn.

---

## §24 — Die Reihenfolge: `effects` zuerst, und der Grund ist der Erzeuger

Der erste Reflex war `costs`, weil es die kleinere Zahl ist. **Das ist falsch:**

> `costs` zählt Ops im **erzeugten** C. Die Ableitung hängt damit am Erzeuger — an denselben
> sechs Verteilern und zwölf Wildcards aus §1, von denen einer Zugriffsbreiten entschied.
> **Eine abgeleitete Kostenzahl erbt jede offene Stelle dort, und zwar UNSICHTBAR:** heute
> fällt eine falsche Absenkung womöglich als Kostenabweichung auf, nach der Ableitung ist
> sie einfach die neue Zahl.

`effects` ist eine **Quellanalyse**. Sie kennt den Erzeuger nicht und kann von ihm nicht
verdorben werden. **462 Stellen gegen 211 klingt nach der größeren Hälfte; technisch ist sie
die kleinere.**

### Eine Korrektur an der Begründung, gemessen

Das Argument lautete: *Gabbro hat keine Rekursion, also ist der Aufrufgraph ein DAG, und
Effektableitung ist ein topologischer Durchlauf statt eines Fixpunkts.*

**Die Prämisse stimmt nicht mehr.** Seit dem 2026-08-19 gibt `decreases` der Rekursion ein
Maß (`beispiele/33`, «K5.4»). Gemessen: **4 Dateien, 6 `decreases`-Stellen.**

> *Bis dahin stand im ganzen Korpus keine einzige rekursive Funktion, und der Grund war kein
> Stilentscheid: `K001` fiel an jeder.*

**Der Schluss überlebt trotzdem, aber aus einem anderen Grund:** Wirkungen bilden einen
endlichen Verband (Vereinigung über eine endliche Ortsmenge), also konvergiert der Fixpunkt
über den Zyklen ohnehin — und bei sechs rekursiven Stellen im ganzen Korpus ist der
Unterschied zwischen topologisch und Fixpunkt keine Kostenfrage. **`aufrufgraph.rs`
existiert schon.**

*Die Zahl `6` gehört in den Auftrag, damit niemand die DAG-Annahme als gegeben mitnimmt.*

> **Das Verbandsargument ist FALSCH, gemessen am Bau (2026-09-01).** Die Ortsmenge ist nicht
> endlich: `aufrufgraph::ersetze` erzeugt beim Tragen über den Aufrufrand neue Orte, und in
> einem Zyklus wächst der Ortsausdruck ohne Schranke. Der Schluss überlebt — mit einer
> **Verbreiterung**, die die Ortstiefe kappt — das Argument nicht. **§38.**

---

## §25 — Was der Plan sonst nicht bepreist: die Diagnose wandert

`[E005] f writes … but declares pure` **existiert nur, weil es eine Deklaration zu
widersprechen gibt.** Ohne sie verschwindet die Fehlerklasse nicht — **sie zieht um**: an
den Aufrufer, an eine Sperrrangprüfung, an eine `extern`-Grenze, an ein `pure` drei Ebenen
höher.

> **Der Fehler entsteht am Rumpf und wird woanders gemeldet.**

Das ist dieselbe Form, die bei `op_zeichen` als Befund steht: *eine Absage, die die Zeile
nicht zitieren kann, um die es geht.* Und `E4` sagt es im Entwurf selbst — Verträge stehen
in fester Ordnung, **damit** ein Werkzeug „hier fehlt `effects`" sagen kann.

**Die Ableitung handelt Lokalität gegen Schreibarbeit.** Das ist bezahlbar, aber es gehört
bepreist:

- [x] Die abgeleitete Menge muss **abrufbar** sein (`gabbro effects <fn>`) — **gebaut
      2026-09-01**, samt `--ursprung`, `--vergleich`, `--sperrrang`, `--eng`.
- [ ] Ein Widerspruch muss den **Ursprung** nennen, nicht nur die Stelle, an der er
      auffällt. *Der Pfad ist rückverfolgbar — das ist keine neue Analyse, nur eine Ausgabe.*
      **Der Pfad steht (`Ableitung::pfad`), in einer Absage steht er nicht** — §41.

---

## §26 — Was nicht verloren gehen darf: die Ratsche

Heute bricht eine Änderung, die eine Funktion teurer macht, **an der Deklaration**. Nach der
Ableitung gelingt sie still und die Zahl ist eine andere. **Die Kostenschranke hört auf, ein
Riegel zu sein.**

Die Heilung ist die, die dieser Baum überall sonst benutzt: **nicht Quellannotation, sondern
gemessene Zahl unter einem Wächter**, wie `377 von 377 Ankern`.

- [ ] `gabbro costs` schreibt in eine Messdatei, ein Wächter vergleicht, **eine
      Verschlechterung ist rot.**

> **Damit ist die Ratsche STÄRKER als heute** — sie deckt dann alle Stellen statt nur die
> 211 deklarierten — und der Nutzer schreibt `costs` nur noch, wo er enger sein will als die
> Messung.

**Die Richtung dieses Satzes stimmt nicht** (gemessen 2026-09-01): in `beispiele/` stehen
**210 `costs <=`-Zeilen** und nur **179 Stellen mit gerechneter Zahl** — die Differenz sind
`extern`/`prim` ohne Rumpf. *Ein gemessener Wächter deckt WENIGER Stellen.* Stärker wird er
in der **Richtung**, nicht in der Fläche: heute dürfen sich **61 % der Rümpfe verdoppeln**,
ohne dass `costs` beisst. **§40 trägt die ganze Rechnung.**

Für `effects` gilt dasselbe in schwächerer Form: eine stille Verbreiterung einer
Blattfunktion verbreitert vierzig Aufrufer, und heute merkt man es an vierzig Stellen.

- [ ] **Ob das Firewall oder Lärm ist, ist messbar:** wie viele der 462 Einträge würden bei
      stiller Verbreiterung etwas ändern, **das der Prüfer nicht ohnehin fängt?** *Falls
      fast keine — Lärm, und der Fall ist gemacht.* **Eine Teilantwort steht in §39:** an
      genau EINER Stelle im ganzen Baum ändert die engere Menge etwas — und die Stelle
      musste gebaut werden, weil der Korpus sie nicht hat.

---

## §27 — Zwei Zweifel an der Einteilung selbst, beide berechtigt

*Ein Durchgang über zwanzig Regeln ist in diesem Baum noch nie ohne zweiten Befund
geblieben.*

### `progress` steht unter T6 und hat die Bauart von T11

```
T6   a loop bound, `on_exceeded`, `progress` or `decreases`
     because: termination is not readable from the body
T11  `assume` with its falsifier
     because: an assumption no probe can contradict is not a statement (`N031`)
```

`forever … progress timer_tick_arrives` **ist eine Umgebungsannahme mit Falsifikator — der
Wachhund IST der Falsifikator.** Das ist T11s Bauart, nicht T6s.

> **Eines von beiden ist falsch einsortiert**, und dann sind es nicht 188 gegen 93.

Dasselbe steht schon in §15 als *„`progress` und `assume` sind dieselbe Sache in zwei
Listen"* — hier trifft es die Zielmarke zum zweiten Mal, **was für den Posten spricht.**

### T12, Bereich am Typ, 26 Stellen

```gabbro
type KernIdx = u32 in 0 ..< NKERNE;        table … count NKERNE
type Tiefe   = u64 in 0 .. 1048576;        table Halde count 1048576
```

**Das ist keine Nutzerlogik, sondern eine zweite Abschrift derselben Zahl.** `index into T`
leitet die Schranke schon aus `count` ab — für diese Aliase tut es niemand.

- [ ] Zählen, wie viele der 26 aus einer Tabellendeklaration ableitbar sind. **Sie gehören
      dann in die Buchführung**, und die Marke wird `188 → weniger`.

> **Beides eher gut als schlecht: die Zielmarke wird SCHÄRFER, nicht schwächer.**

---

## §28 — Die Bahn, und was vor ihr steht

| | |
|---|---|
| **steht schon** | §23, die Polsterungsmessung — **87 % gepolstert, 397 über 50 %** |
| **1** | ~~**`effects` ableiten**~~ — **GEBAUT 2026-09-01**, `crates/gabbro-check/src/ableitung.rs`. Nicht 462 Stellen, sondern **359 vergleichbare**; siehe §38 |
| **2** | ~~`gabbro effects <fn>` + Ursprungspfad~~ — **GEBAUT**, `--ursprung` läuft. *Aber in keiner Absage* — §41 |
| **3** | `costs` unter einen Wächter (§26) — **die Rechnung steht in §40, gebaut ist nichts** |
| **4** | `costs` ableiten — **nach** §1, weil die Zahl sonst die Wildcards erbt |
| **5** | §27 klären: `progress`/T11, und wie viele der 26 T12 Abschriften sind |

> **Und keine einzige Deklaration ist gefallen.** Was steht, ist der Zwischenzustand aus §1
> des Auftrags — beide Register über derselben Sache, vergleichbar. *Die Marke `705 → 0` ist
> unbewegt.*

**Und die Marke steht, bevor gebaut wird: `705 → 0`, `188` bleiben.** Sie kann fallieren,
und das ist der Punkt.

---

# TEIL V — Die Beweisseite, die Teil IV nicht misst

*Angefügt 2026-09-01. **Teil IV misst SCHREIBLAST.** `705 → 0` heißt: der Nutzer *schreibt*
nur noch seine Logik. **Ob er sie BEWEISEN kann, steht auf einem anderen Blatt** — und die
Zahlen dort sind schlechter.*

## §29 — „Nur noch seine eigene Logik beweisen" hat zwei Hälften

Die Zeremoniemessung deckt die erste ab. Vier Posten stehen daneben, und **keiner davon
taucht in den 1054 Stellen auf.**

*Gemessen 2026-09-01 über die 159 Dateien ohne `gift/`:*

```
  Kanal A  Pflichten     112 Register ueber 159 Dateien     92 Pflichten
                         47 Dateien tragen KEIN Register
  Kanal B  Ruempfe       145 GETRAGEN, 236 ABGELEHNT        145/381 = 38 %
  Absenkung              `Absenkung_Parametrisch.thy` deckt EINE erzeugte Form
```

> **Eine Einheit mit Fehlern trägt kein Register.** 47 von 159 — und das ist keine
> Nachlässigkeit, sondern Bauart: **wo der Prüfer absagt, gibt es nichts zu beweisen.**
> *Aber es heißt auch: die Beweisseite sieht nur, was die Prüfseite schon durchgelassen hat.*

---

## §30 — Ausdrückbarkeit: er muss sie sagen können

Die schärfste Fundstelle steht im eigenen Baum: **Spezifikation 2 ist ein Quantor** —
*„`raeumen` fasst kein anderes Fach an"* — **und eine `spec fn` kann das nicht.**

> **Rahmenbedingungen sind der häufigste Inhalt einer Kernspezifikation, und für sie muss
> der Nutzer heute die Sprache verlassen.**

Dazu drei ausdrückliche Streichungen, jede einzeln begründet:

```
keine Rekursion in `spec fn`  ·  keine handgeschriebenen Lemmata
keine benutzerdefinierten Quantorendomaenen
```

**Zusammen bilden sie eine Decke**, und das offene Item sagt selbst: *ein einziger Fall in
der letzten Spalte setzt sie tiefer.*

### Die härteste Form sieht man erst bei n > 1

> **Wenn eine neue Datenstruktur ein neues Domänenwort braucht, braucht der Nutzer den
> SPRACHAUTOR.**

Das ist der äußerste Gegensatz zu „nur seine eigene Logik": **sein Problem ist dann nicht
unbeweisbar, es gehört jemand anderem.**

**Darum ist die deklarierte Erreichbarkeitsdomäne (§12) der Vorschlag mit dem größten Hebel
auf genau dieses Ziel** — nicht wegen der siebzehn Wörter, sondern weil sie die Abhängigkeit
vom Sprachautor auflöst.

---

## §31 — Vertrauen: er darf nicht glauben müssen, dass das C sein Programm ist

> **Wenn er seine Logik über der Quelle beweist und die Maschine etwas anderes ausführt, hat
> er nichts bewiesen.**

Heute deckt der Absenkungssatz **eine** erzeugte Form — und *die Instanz, an der er geprüft
wurde, war an einem Zweig falsch* (`ab32267`).

Drei Teile, alle offen:

- [ ] **Absenkungsabdeckung** — alle erzeugten Formen. Heute eine. *Der Nenner steht in §1
      Teil I: 64 Formen im Erzeugnis.*
- [ ] **Die Naht zwischen den Beweisern.** Der Satz *„das erzeugte C erfüllt die
      Lean-Spezifikation"* **existiert in keiner Logik.** Er entsteht durch Nebeneinanderlegen
      von Isabelle (3512 Z, 101 Sätze) und Lean (4068 Z, 155 Sätze) — **und das ist kein
      Beweisschritt.**
- [ ] **Unabhängigkeit.** `lean.rs` liegt im Prüfer-Crate, teilt also **auch ungetort den
      Vorderbau**. *Der Fall, für den man einen Verifizierer will, ist der, in dem Prüfer und
      Spezifikation uneins sind — und der kommt heute nicht bis zur Frage.*

> **Das ist der Posten mit dem höchsten Rang in Teil V.** Er ist keine Zeremonie und taucht
> in keiner der 1054 Stellen auf, **aber er entscheidet, ob der Beweis des Nutzers etwas
> über seine Maschine sagt.**

---

## §32 — Die 93 Hardwarestellen skalieren falsch

`assume` mit Falsifikator, Registerklasse, `reserved` — **das kommt aus dem Handbuch, nicht
aus dem Kopf des Nutzers, und keine Ableitung nimmt es ab.**

Aber: **es müsste EINMAL PRO GERÄT anfallen, nicht einmal pro Programm.**

Heute gibt es **keinen Mechanismus, eine geprüfte Gerätebeschreibung samt ihrer Annahmen als
wiederverwendbare Einheit auszuliefern.**

> Solange es keinen gibt, **verlängert jeder neue Treiber die Vertrauensbasis** — und die
> Marke aus §33 ist unerreichbar **aus strukturellen Gründen, nicht aus Sorgfaltsgründen.**

- [ ] `arch` an `assume` (steht schon in §3 und §15 — **dritte Fundstelle**).
- [ ] **Eine Importform, die die Annahmen MITTRÄGT statt sie zu kopieren.** *Hängt an der
      Modulauflösung, die seit `ccf77f2` steht.*

---

## §33 — Die vierte Marke, die heute niemand misst

> **Annahmen bei Programm n+1 gegenüber Programm n.**

**Wenn die nicht null ist, ist „nur noch seine Logik" auch bei perfekter Schreib- und
Beweisseite falsch.**

- [ ] Messen. Es gibt heute kein Werkzeug dafür, und es ist billig: `assume`-Stellen je
      Programm, gegen die Menge der schon im Baum stehenden.

---

## §34 — Was gar nichts trägt

Aus den eigenen offenen Punkten, unverändert gültig:

* Die Naht **CPU ↔ Gerät** hat kein mechanisiertes Modell.
* Der **`iasm`-Eintrittspfad** hat keinen nachgelagerten Beweiser — *161 Stellen auf eine
  geschrumpft, nicht verschwunden.*
* **Lebendigkeit und Fortschritt** fallen unter keinen Mechanismus.
* **Die Ghost-Theorie-Schablonen** sind die vertrauenskritischste Fläche und stehen noch
  nicht in Isabelle.

> **Die letzte ist stiller als die anderen: eine Schablone, die für alle Programme gilt, ist
> ein Fehler, der für alle Programme gilt.**

---

## §35 — Die Zahlenreihe, vollständig

Teil IV misst die Schreibseite. **Die Beweisseite braucht drei Marken daneben, und alle drei
existieren schon als Messung:**

| Seite | Marke | heute | Ziel |
|---|---|---|---|
| **schreiben** | Buchführung gegen eigene Logik | **705 / 188** | **0 / 188** |
| **beweisen** | Pflichten mit Register | 112 Register, **47 ohne** | 159 / 159 |
| **beweisen** | getragene Rümpfe (Kanal B) | **145 / 381 = 38 %** | 381 / 381 |
| **beweisen** | erzeugte Formen mit Absenkungssatz | **1 von 64** | 64 / 64 |
| **skalieren** | **Annahmen bei Programm n+1** | **ungemessen** | 0 |

> **Und die vierte Zeile ist die, die die anderen drei entwertet, wenn sie nicht null wird.**

*Alle Zahlen 2026-09-01 über die 159 Dateien ohne `gift/`. Der Nenner ist genannt, weil er
das Ergebnis entscheidet (W25) — über den ganzen Korpus mit Giftproben sähen sie anders und
schlechter aus, und das wäre keine Messung, sondern eine Verwechslung.*

---

## §36 — Die Annahmen, vorab vermessen: zwei Ebenen, nicht eine

*Gemessen 2026-09-01 über die 159 Dateien ohne `gift/`, alles vor der ersten Zeile Bahn.*

### Wiederverwendung

```
  40 `assume`-Stellen, 31 verschiedene TEXTE
     1x vorkommend   26 Texte    26 Stellen
     2x vorkommend    4 Texte     8 Stellen
     6x vorkommend    1 Text      6 Stellen
                                 --------
     Kopien: 14 von 40 Stellen  (35 %)
```

**Und die Kopien sind genau die allgemeinen:**

```
6x  „Der Zeitgeber unterbricht; ohne ihn laeuft ein Durchgang bis zum Wachhund"
        04-schleifen · 39-auftragsdienst · 41-handschlag · 42-zaehlwerk · …
2x  „Ein Traeger im dma-Raum ist kohaerent: …"                02-geraet · F04
2x  „Nach SRTP=1 steht RTPS=1, bevor TE gesetzt werden darf."  02-geraet · 09-ohne-zeiger
```

> **„Der Zeitgeber unterbricht" ist keine Aussage über `04-schleifen` oder `41-handschlag`
> — sie ist eine Aussage über die PLATTFORM. Sie steht sechsmal, weil es keinen Ort gibt,
> an dem eine Plattformaussage einmal stehen kann.**

### Damit sind es ZWEI Ebenen, und §32 nannte nur eine

| Ebene | Beispiel | müsste stehen |
|---|---|---|
| **Gerät** | `SRTP=1 → RTPS=1`, `dma_kohaerent`, `GCMD`-Schreibvorgang | **einmal pro Gerät** |
| **Maschine** | Zeitgeber, `CR3` verwirft, Release-Speichern, IPI-Zustellung | **einmal, Punkt** |

> **Die zweite Ebene gibt bei Programm n+1 den Ausschlag.** Ein neues Programm auf derselben
> Maschine darf **gar keine** neue Plattformannahme erzeugen — **und heute erzeugt es sechs
> von sechs.**

### Die Marke, geschärft

Statt *„Annahmen pro Programm konstant"*:

> **Plattformannahmen pro Programm NULL. Geräteannahmen pro Gerät EINMAL.**

**Beide sind fallierbar, und die erste ist heute schon widerlegt.**

### Die Vorabprobe für die 26 Einzeltexte

*Ohne Programm n+1 auszukommen: **nennt der Text einen Namen aus seiner eigenen Datei?***
Eine Annahme, die eine bestimmte Tabelle oder Funktion nennt, sagt etwas über die Welt in
den Begriffen eines Programms — **und ist vermutlich zu eng formuliert.**

```
  EINZELTEXTE  26:   7 nennen einen Namen aus der eigenen Datei  (27 %)
  KOPIERTE      5:   1 nennt einen                               (20 %)
```

**Neunzehn von sechsundzwanzig sind echte Weltaussagen**, und neun davon stehen in
`06-annahmen.gab`:

```
  Ein Schreiben auf CR3 verwirft die nicht-globalen Eintraege.
  Ein gesendetes IPI erreicht den Zielkern in endlicher Zeit.
  Ein Release-Speichern macht jede vorher geschriebene Nutzlast sichtbar.
  Die MMU setzt in einem Seitentabelleneintrag ausschliesslich …
```

> **§35 ist damit entspannter als befürchtet:** die Einzeltexte sind überwiegend echte
> Einzelfälle, nicht verkappte Programmaussagen.

**Und die sieben Treffer sind zum Teil ein Fehler meines Maßes**, nicht der Texte:
`USED_IDX`, `GCMD`, `FSTS` sind **Registernamen aus dem Handbuch**, die zufällig auch in der
Datei deklariert stehen. *Das Maß fängt den Namen, nicht seine Herkunft* — dieselbe Gestalt
wie überall. Genuin programmförmig sehen **zwei** aus (`Manifest`, `Statusregister`+`fertig`).

---

## §37 — Überdeklaration: still, unauffällig, und sie macht den Prüfer STRENGER

```gabbro
impl fn zuviel(t : ptr<normal,rw> T, u : ptr<normal,rw> U, i : index into T) -> u32
    effects { reads t.slots, writes t.slots, reads u.slots, writes u.slots }
{ return t.slots[i].a; }              ->   5 items, 0 errors, 0 hints
```

**Zwei Tabellen deklariert, eine angefasst, kein Wort.** Das ist `costs <= 100000` auf der
Effektseite — **aber schärfer:**

> Bei `costs <= 100000` steht die Zahl da; ein Leser sieht sie und kann stutzen. Bei
> `reads u.slots` auf eine nie berührte Tabelle sieht der Leser **eine Klausel, die aussieht
> wie jede andere.** Die Überdeklaration ist nicht nur ungemessen — **sie ist unauffällig.**

### Und sie hat eine Folgewirkung, die die Kostenseite nicht hat

`effects` speist **den Sperrrangpass, `touches`, die Nebenläufigkeitsargumente.**

> Eine zu weite Effektmenge macht den Prüfer nicht falsch, aber **strenger als nötig** — sie
> kann eine korrekte Sperrreihenfolge ablehnen, **weil eine nie berührte Tabelle im Rahmen
> steht.** Ein Fehlalarm derselben Klasse wie `L104`, eine Ebene höher — **und niemand würde
> ihn als solchen erkennen, weil die Klausel ja dasteht.**

- [ ] **Nebenmessung nach der Ableitung:** geht eine der heute abgesagten Rangprüfungen unter
      der engeren Menge durch? *Das wäre der Beleg, dass Überdeklaration nicht Zeremonie ist,
      sondern Reibung.*

### Ein zurückgezogenes Maß, und der Rest, der bleibt

Ein textueller Versuch — *Basisname kommt im Rumpf nicht vor* — gab `103 von 527 (20 %)`,
davon `53` ohne Ruf im Rumpf. **Die 53 sind falsch und zurückgezogen:**

```gabbro
impl fn liegt_unter(…) effects { reads Topologie.slots, locks TOPO }
{ traverse v of g over ancestors of g { … } }
```

Der Rumpf fasst `Topologie.slots` **durch die Domäne** an, ohne den Namen zu schreiben.
Ebenso `PLANER` über `requires Held(PLANER)`.

**Aber der Befund darunter bleibt, und er ist die Struktur hinter der toten Zahl:**

> **Es gibt ZWEI Wege, auf denen ein Ort ohne seinen Namen in den Rumpf kommt — die Domäne
> und der Gerufene.** Die 53 sind der erste Weg, die 50 mit Ruf der zweite. *Und nur den
> zweiten rechnet eine Ableitung über den Aufrufgraphen von selbst.*

**Damit ist die Frage, ob die 462 Abschriften stimmen, bis zur Ableitung unbeantwortbar** —
und das ist selbst das Argument für den Zwischenschritt aus §28.

---

## §38 — Der Zwischenzustand, GEMESSEN — und drei Zahlen dieses Teils sind falsch

*Angefügt 2026-09-01, nach dem Bau von `crates/gabbro-check/src/ableitung.rs`. §37 sagt, die
Frage sei „bis zur Ableitung unbeantwortbar". **Sie ist jetzt beantwortet.***

### Die Grundgesamtheit ist nicht 462

`gabbro abi --vergleich` und `gabbro effects --vergleich` zählen jetzt **je Eintrag** statt
je Funktion. Über `beispiele/*.gab` (62 Dateien):

```
  effects-Eintraege an einer Funktionsdeklaration     439   (AST, massgeblich)
      auf einer Funktion MIT Rumpf                    359   (170 Funktionen)
      auf `extern`/`prim` -- OHNE Rumpf                80   ( 69 Funktionen)

  effects-Eintraege ueberhaupt (Textzaehlung)         538
      der Rest steht an `forever`, `retry`, `axiom`,
      `transition` und an FUNKTIONSZEIGERTYPEN
```

> **Die 80 können nie auf null gehen.** Kein Rumpf, nichts abzuleiten — die `effects`-Zeile
> eines `extern fn` ist die **Vertrauensfläche**, keine Buchführung. Sie in die Marke zu
> zählen verspräche eine Ersparnis, die kein Bau liefern kann.

**Und die 462 aus §21 sind keine dieser Zahlen.** Der Satz dort nennt 64 Dateien; welche zwei
über `beispiele/` hinaus und welche Träger mitgezählt sind, steht nirgends. *Bis das
nachgetragen ist, ist 462 eine Jahreszahl* — die belastbare Zahl ist **359 vergleichbare
Einträge**.

### Die Vergleichszahl

Zwei Basen, dieselben Urteilsregeln (`deckt_a4`, `Urteil`), damit der Unterschied die Basen
misst und nicht die Regeln:

```
                                Huelle ueber       Ableitung ueber
                                DEKLARATIONEN      RUEMPFE
  STIMMT   deckt Abgeleitetes        263                264
  STIMMT   `pure`, Menge leer         28                 28
  ZU WEIT  deckt nichts               57                 59
  ZU ENG   `pure` widerlegt            4                  4
  ausserhalb `diverges`                4                  4
  UNGEMESSEN, Huelle reisst (R16)      3                  0
  ------------------------------------------------------------
                                     359                359

  ZU ENG -- abgeleitet, von keiner Zeile gedeckt
                                      31                 39
```

**~~59 von 359 — 16 % — tragen nichts.~~ ZURÜCKGEZOGEN am 2026-09-01, nicht korrigiert.**

> `huelle_der_gerufenen` nimmt vom Gerufenen seine **deklarierten** Effekte und **vererbt
> damit dessen Polsterung an den Rufer — sie deckt genau den Fehler zu, den sie finden
> soll.** Liegt die Hüllenrechnung auf dem Messpfad, ist die Zahl **systematisch nach unten
> verzerrt: je gepolsterter der Gerufene, desto weniger fällt der Rufer auf.** Bei 87 %
> gepolsterten Kostenzusagen ist das kein Randeffekt.
>
> **Und darum ist sie keine untere Schranke, sondern unbekannt.** *Eine Zahl aus einem
> Werkzeug mit bekanntem Maskierungsfehler ist nicht vorsichtig, sie ist unbelegt.* Sie wird
> nach der Reparatur neu gefahren, nicht nachgerechnet.

**Vierte Instanz derselben Gestalt in zwei Tagen:** der maskierende `panic!` (der erste
Treffer verdeckt jeden späteren) · die Namenszählung statt Ortserreichung (`ancestors of`
fasst an, ohne zu nennen) · Handbuchnamen als Programmnamen gelesen · **jetzt die Hülle.**

Was von der Messung STEHT: `E005` feuert bei Widerspruch, **nicht bei Auslassung** — und
Überdeklaration ist gemessen still. *Der Mangel ist belegt, sein Umfang nicht.*

*Ohne `--weit`* — also mit der Filterung, die `E010` selbst anlegt — stünden dort 95 statt
57. **Das wäre ein Messfehler und keine Polsterung:** die Ableitung liesse dann Lesungen über
Parameter aus, und jedes deklarierte `reads t.slots` sähe wie Überdeklaration aus. *Ein
Erzeuger, der die Zeile SCHREIBT, muss `reads p.slots` schreiben — der Aufrufer will wissen,
was mit seinem Zeiger geschieht.*

Die 4 widerlegten `pure` und die 39 ungedeckten Abgeleiteten sind **kein Rahmenbruch**: die
Funktionstafel weist sie als *„no known world name — `E008`/`E010` stay silent, with
reason"* aus.

### §24 sagt „endlicher Verband", und der Verband ist nicht endlich

> *„Wirkungen bilden einen endlichen Verband (Vereinigung über eine endliche Ortsmenge), also
> konvergiert der Fixpunkt über den Zyklen ohnehin."*

**Die Ortsmenge ist nicht endlich.** `aufrufgraph::ersetze` trägt einen Ort über den
Aufrufrand, indem es den Parameternamen durch den Argumentausdruck ersetzt — in einem Zyklus
wächst er:

```
writes k.wert  ->  writes k.kind.wert  ->  writes k.kind.kind.wert  ->  …
```

*Der Verband ist endlich, solange niemand neue Orte erzeugt; genau das tut die Brücke über
den Aufrufrand.* Die Ableitung trägt deshalb eine **Verbreiterung**: ein Ort tiefer als vier
Schritte wird auf sein Präfix gekürzt — grob in die sichere Richtung, weil `deckt` über
Präfixe arbeitet. **Sie feuert im ganzen Korpus 0×**, und die Zahl steht in jeder Ausgabe.

**Der Schluss aus §24 überlebt, das Argument nicht.** Und was die Ableitung dafür KANN:

```
beispiel::rekursion   Huelle:    incomplete -- «cycle over `absteigen`»
                      Ableitung: effects { writes summe }
```

`UNGEMESSEN` fällt von 3 auf 0.

### Ein vierter Fall einer bekannten Klasse

Der Aufrufgraph trägt Knoten, die **keine `fn`-Items** sind: Geräteübergänge, Gerätegriffe
und **erzeugte Tabellenops**. `aufrufgraph.rs` nennt die ersten beiden *„eine Lücke im
GRAPHEN, nicht im Programm"* und die dritte *„dritte Instanz derselben Reparatur an derselben
Stelle"*. **Die erste Fassung der Ableitung sah sie nicht** — 18 Funktionen meldeten
„unknown to the graph" gegen 3 bei der Hülle. *Gefunden, weil zwei Basen nebeneinanderstanden.*

Sie bekommen einen eigenen Herkunftsweg (`Vertrag`), nicht `Rand`: **`Rand` heisst „hier hört
die geprüfte Welt auf", `Vertrag` heisst „hier hat der Übersetzer die Zeile schon
geschrieben".** Ein erzeugtes `T::insert` in die Vertrauensfläche zu zählen blähte die nicht
entfernbare Hälfte der Marke mit Einträgen auf, die nie jemand getippt hat.

---

## §39 — Die Reibung ist belegt, und `H012` liest eine Erlaubnis als Erwerbung

*§3 des Auftrags: geht eine heute abgesagte Rangprüfung unter der engeren Menge durch?*
**Ja — aber der erwartete Weg ist versperrt, und zwar von einem Wächter, den es schon gibt.**

Die Vermutung lautete: eine zu weite Menge nennt eine nie berührte Sperre, `H012` sagt
deshalb eine richtige Reihenfolge ab. **Der direkte Fall fällt schon:**

```
[H011] `helfer` declares `locks KLEIN` but never takes it
```

*Überdeklaration von `locks` ist also NICHT still.* Offen bleibt der Weg, den `H011`
ausdrücklich zulässt — eine Zeile, die durch `requires Held(…)` eingelöst wird, *„the
caller's duty"*. Und dort lesen zwei Pässe dasselbe Wort verschieden:

| | |
|---|---|
| `H007` liest | *„`X` ist hier GEHALTEN"* — eine **Erlaubnis** |
| `H012` liest | *„dieser Aufruf NIMMT `X`"* — eine **Erwerbung** |

Für eine Funktion mit `requires Held(X)` ist die zweite Lesart **falsch**. `H012` holt sie
sich über `Rufwissen::nimmt` → `aufrufgraph::huelle` trotzdem.

`messung/proben/460-rangprobe-an-zu-weiter-wirkung.gab`: `KLEIN` Rang 1, `GROSS` Rang 2, **in
der richtigen Reihenfolge genommen**, darin ein Ruf auf eine Funktion, die `KLEIN` nur
verlangt.

```
$ gabbro effects --sperrrang beispiele/*.gab beispiele/gift/*.gab messung/proben/*.gab
  units read                                   446
  rank refusals that stand in BOTH               5
  rank refusals the derivation FREES             1
      H012 …/460-rangprobe-an-zu-weiter-wirkung.gab
  rank refusals only the derivation raises       0
```

**Die fünf Giftproben behalten ihren Biss** — die Ableitung nimmt einem `extern fn` seine
Deklaration nicht weg, sie IST dort die Quelle. **Und die dritte Spalte ist leer, wie sie sein
muss.**

> **Im heutigen Korpus kommt keine Absage frei; der Fall musste gebaut werden.** Der Grund ist
> nicht, dass es ihn nicht gibt, sondern dass keine Korpusdatei ein `requires Held(X)` unter
> eine höherrangige Sperre stellt. *Das ist eine Aussage über den Korpus, nicht über die
> Sprache* — und der `H012`-Befund steht auch ohne jede Ableitung.

---

## §40 — Was ein `costs`-Wächter kostete, und §26 hat die Richtung falsch

*§4 des Auftrags: **nur die Rechnung, kein Bau.** Gemessen 2026-09-01 über 522 `.gab`-Dateien
mit `gabbro costs`.*

### Die Grundgesamtheit

```
  Stellen mit gerechneter Zahl                       718
      davon slack >= 0                               697
      davon slack <  0                                21   <- 20 Giftproben + `33-rekursion`
  Der ganze Lauf ueber 522 Dateien                   0,6 s
```

*Die eine saubere Datei mit negativem `slack` ist `beispiele/33-rekursion.gab`: `absteigen`
rechnet 70 gegen zugesagte 64, weil ein Zyklus die Zusage EINES Durchgangs meint («K5.4»).
`pruefe` sagt dazu nichts — **eine Stelle, an der `costs` und `gabbro costs` verschieden
rechnen, und das steht bisher nirgends.***

### Was die Schranke heute NICHT hält

```
  Summe slack ueber 697 Stellen             491 574 ops
  Median slack                                    4 ops
  Mittel                                        705 ops        <- die Verteilung ist schief
  Zusage / gerechnet     Median 2,62   Mittel 11,9   Max 1562

  Stellen, an denen der Rumpf sich VERDOPPELN darf,
  ohne dass `costs` beisst                        423   (61 %)
  ... verZEHNfachen                                75   (11 %)
```

> **An 61 % der Stellen darf der Rumpf doppelt so teuer werden, ohne dass ein Wächter
> aufwacht.** Das ist die Ratsche, die §26 erhalten will — sie hält heute an drei von zehn
> Stellen etwas.

### Was ein gemessener Wächter kostete

| | |
|---|---|
| **Messdatei** | 718 Zeilen, ~10 KB — je Stelle `modul::name` und die gerechnete Zahl |
| **Laufzeit** | **0,6 s** über den ganzen Korpus, gegen 23 min für den vollen Lauf |
| **Bau** | ein Schreibmodus an `gabbro costs` und ein Vergleichsskript nach dem Muster von `377/377` |
| **Pflege** | *ungemessen* — wie oft eine legitime Änderung eine Zeile bewegt, sagt nur ein Lauf über die Historie |

### Und §26 hat die Richtung falsch

> §26: *„Damit ist die Ratsche STÄRKER als heute — **sie deckt dann alle Stellen statt nur
> die 211 deklarierten**."*

**Das stimmt nicht.** In `beispiele/` stehen **210 `costs <=`-Zeilen** und nur **179 Stellen
mit gerechneter Zahl** — die Differenz sind `extern`/`prim` ohne Rumpf, dieselbe Struktur wie
bei `effects`. *Ein gemessener Wächter deckt WENIGER Stellen, nicht mehr.*

**Stärker wird er in einer anderen Achse, und die ist die wichtigere:**

| | heute | mit Wächter |
|---|---|---|
| **Stellen** | 210 (auch ohne Rumpf) | 179 (nur mit Rumpf) |
| **Richtung** | nur Überschreiten einer gepolsterten Decke | **jede Bewegung, in beide Richtungen** |
| **Auflösung** | 61 % dürfen sich verdoppeln | eine einzige Op fällt auf |

*Die Zusage bleibt daneben nötig — für die 31 Stellen ohne Rumpf ist sie das Einzige, was es
gibt.* **Was fällt, ist die Pflicht, sie überall hinzuschreiben; was bleibt, ist das Recht,
sie enger zu setzen als die Messung.**

---

## §41 — Was nach diesen drei Bahnen UNGEMESSEN bleibt

* **Die Marke selbst ist nicht bewegt.** Gebaut ist die Ableitung und ihre Messung; **keine
  einzige Deklaration ist gefallen.** `705 → 0` steht unverändert offen.
* **Der Erzeuger ist nicht angefasst** — richtig so (§24), aber damit ist auch nicht
  gemessen, was eine abgeleitete `costs`-Zahl von den zwölf Wildcards erbte.
* **Ob die Ableitung als PFLICHT trägt, ist offen.** Sie rechnet heute neben den Pässen; ob
  `E005`/`E008`/`E010` mit ihr statt mit der Deklaration dasselbe sagen, ist nicht gefahren.
* **Die Verbreiterung ist im Korpus nie gelaufen** (0×). Dass sie funktioniert, sagt eine
  Probe, nicht der Korpus.
* **Der Ursprungspfad ist abrufbar, aber in keiner Absage.** `E005` nennt ihn nicht; §25
  verlangt es für den Zustand NACH dem Fall der Deklaration, und der ist nicht da.
* **Die Zahl 462 ist nicht rekonstruiert** — 439 an Funktionen, 538 überhaupt, und welche 64
  Dateien §21 meinte, steht nirgends.
* **Die Pflegekosten eines `costs`-Wächters sind nicht gemessen**, nur seine Laufzeit.
* **`progress`/T11 und die 26 T12-Abschriften (§27) sind unberührt.**

---

# TEIL VI — Fünf Vorschläge, und sie müssen sich gegen die Ratsche rechtfertigen

*Angefügt 2026-09-01. **Drei der fünf sind selbst Wörter.** Der Wortschatz ist an einem Tag
um acht gewachsen, während der Absenkungssatz bei eins blieb — also gilt hier, was §11
verlangt: jedes muss nennen, welches Wort es ablöst oder warum keine vorhandene Form es
trägt. Sortiert nach diesem Handel, nicht nach Reiz.*

## §42 — ~~`phase` verallgemeinern · **der einzige, der den Wortschatz SENKT**~~ **NACHGERECHNET UND ABGELEHNT**

> **Ausgerechnet am 2026-09-01, Regel A, und die Rechnung trägt nicht:
> `messung/PHASENKONSTRUKT.md`.** Es fällt **EIN** Wort (221 → 220), nicht vier. Der
> versprochene Absenkungssatz ist **null statt null** — eine Geistmarke senkt nichts ab.
> Zwei der vier „weiteren Stellen" haben das Konstrukt schon, eine braucht keines, eine ist
> kein Gang, sondern ein Baum. **Und die vier Zahlen unten sind über dem Giftkorpus
> erhoben.** *Der Rest dieses Abschnitts steht als Gegenstand der Rechnung, nicht als
> Vorschlag.*

`class rw in setup, r in live` über `linear ghost type QueuePhase order { setup, live }` ist
heute an `reg` gefesselt. **Der Mechanismus dahinter ist allgemein: eine lineare, geordnete
Geistermarke schaltet erlaubte Operationen.**

*Gemessen 2026-09-01 — das Muster liegt schon breit im Baum:*

```
linear ghost type … order { … }     14      -> im Ratschenkorpus: 3   (11 in `gift/`)
advances <a> -> <b>                 31      -> im Ratschenkorpus: 12  (19 in `gift/`)
class … in <phase>                   6      -> im Ratschenkorpus: 3   (4 in `gift/`)
consumes …                         102      -> im Ratschenkorpus: 52  (50 in `gift/`)
```

> **Die Grundgesamtheit stand nicht dabei, und sie ist der erste Befund.** Die Zahlen sind
> über **alle 526 `.gab`** erhoben, darunter die **357 Giftproben**. Die Ratsche, gegen die
> dieser Vorschlag sich rechtfertigen muss, misst über **164**. *Eine Giftprobe ist ein
> Programm, das FALLEN soll — wie oft ein Konstrukt darin steht, misst die Gründlichkeit der
> Begiftung und nicht den Bedarf.* **Elf der vierzehn `order`-Deklarationen sind Giftproben;
> das Konstrukt liegt in drei echten Programmen.**

~~**Vier weitere Stellen tragen dasselbe Muster ohne Konstrukt:**~~ **Zwei davon tragen es
MIT Konstrukt, und die Nachrechnung steht rechts:**

| geschrieben | nachgeschlagen |
|---|---|
| **`count`/`backed`** — nach dem Wiederwachsen *uninitialisiert*, dann *beschrieben*; „die fehlende Initialisierungspflicht aus §5 IST eine Phase" | **braucht keines.** `PLAN.md`:2577–2580 hat es entschieden: *„entweder **monoton** … oder das Verkleinern ist ein Phasenschritt … **Für das Zweite gibt es die «B37»-Maschinerie schon (`order`/`advances`), und für das Erste braucht es nichts.**"* — *und die §5 hier trägt Seitentabellen und W⊕X, nicht die Hinterlegung* |
| **Eine Capability im CDT** — abgeleitet, delegiert, widerrufen | **die einzige echte Lücke — und `phase` schließt sie nicht.** Eine `order` liegt auf EINER Marke, `phasen.rs` verfolgt sie je Rumpf und je Variable; ein Widerruf läuft rekursiv über einen **Baum**, und `O002` prüft einen Vorwärtsschritt zwischen zwei Stufen |
| **`boot`** — vor und nach `bss_nullen` | **hat das Konstrukt.** `beispiele/22-bootstrecke.gab`:55 führt `order { roh, mmu, caps, eps, autoritaet, dienste }` und **sechs** `advances`-Zeilen |
| **Speicher zwischen Kern und Gerät** — *„wofür `consumes` plus Phase heute von Hand kombiniert wird, 102 Mal"* | **umgekehrt.** Von 104 `consumes` stehen **30** in einer `fn`, die `advances` trägt — *das ist das Konstrukt, nicht seine Handnachbildung*. Die **74** anderen haben gar keine Phase: eine Sperre, ein Zeuge, ein weggegebener Puffer |

> ~~**Ein Konstrukt `phase`, auf `table`, `ops`, `fn` und `reg` anwendbar, ersetzt Sonderregeln
> in vier Bereichen und bekommt EINEN Absenkungssatz statt vier.**~~
>
> **`table` und `ops` haben keinen Wert in einer Signatur, durch den eine Stufe fließen
> könnte.** Ein `phase` dort ist `PHASENKLASSE.md` §2 **Form 3**, am 2026-08-28 mit Grund
> abgelehnt: *„eine BEHAUPTUNG des Rufers, keine Tatsache"* und *„ein ZWEITER Mechanismus
> neben der Ordnung (W7)"*. **Und die vier Absenkungssätze gibt es nicht:** `emit.rs`:44
> *„ghost types (they lower to NOTHING)"*, `PHASENKLASSE.md` §4 *„Sie senkt nichts ab."*
> *Viermal nichts ist nichts, und einmal nichts auch.*

*Der Name in der Literatur ist **Typestate**. Dass er hier unabhängig für Register gefunden
wurde, spricht dafür, dass er in der Domäne liegt* — und `SPRACHE.md`:100 bucht ihn seit
jeher als **M2**, *„linear value whose type carries the state"*: **eine Ableitung, kein
Konstrukt. Dort steht er richtig.**

- [x] ~~**Nach der Domänenregel der zweitbeste Eröffnungsfall für die Ratsche**~~
      **NICHT GEBAUT, und die Absage ist das Ergebnis** (2026-09-01,
      `messung/PHASENKONSTRUKT.md`). Er senkt die Wortzahl, aber **um eins**: `order` und
      `advances` sind der ganze Bestand (`phasen.rs`:29 — *„Der Wortschatz waechst um `order`
      und `advances` — einmal, nicht je Schritt"*), `phase` kommt dafür, `class`/`in` an
      `regphasen` kosten heute schon nichts, und `consumes` bleibt für seine 74 phasenfreien
      Stellen. **Ein Wort ist zu wenig dafür, eine vier Tage alte Begriffsentscheidung
      zurückzunehmen.**
- [ ] **Der Satz, der bleibt, ist keiner dieses Abschnitts:** ein **Erhaltungssatz über der
      Stufenverfolgung** (Bauart `Table_Ops_Erhaltung.thy`, nicht
      `Absenkung_Parametrisch.thy`). Er hängt an einer operationalen Semantik des
      Phasenflusses, an der Löschungsaussage als Theorie und am Schnitt im Wortlaut — **drei
      Dinge, die es nicht gibt.** *Er ließe sich schreiben, ohne dass ein Wort dazukäme oder
      fiele, und gehört damit unter §31.*

## §43 — `ghost` und `witness` trennen · **ein Widerspruch, keine Lücke**

Die drei fehlenden Absenkungen aus §31 kamen aus einem Widerspruch:
**`Griff(index into Arena)` ist als `ghost` deklariert und trägt einen Nutzdatenwert, den das
C braucht.** Geistern und Datentragen sind zwei Dinge, und ein Wort erledigt beides.

```
ghost     wird geloescht, hat keine C-Form, existiert nur fuer den Pruefer
witness   bleibt im C, ist linear, nur lesbar, sein Nutzdatenwert ist ein gewoehnlicher Wert
```

> Damit ist `Griff` ein `witness`, ~~**die Absenkung ist trivial — der Index steht ohnehin im
> C**~~ — und die Erasure-Regel für `ghost` bleibt unangetastet statt einen Sonderfall zu
> bekommen.

> **Die durchgestrichene Hälfte war am Tag vor diesem Vorschlag schon widerlegt**
> (`messung/proben/probe-zeugenpflicht.gab`:33–58, gemessen 2026-08-31):
>
> *„**Gemessen stimmt das nicht.** `Griff` ist `ghost` und wird vor der Codeerzeugung
> geloescht — sein Nutzdatenwert mit ihm. … Der Zeuge ist weg; der Index ueberlebt **nur,
> weil er als eigenes Argument danebensteht.** … **Drei fehlende Absenkungen, nicht eine**,
> und die tragfaehige kostet ein Maschinenwort je Zeuge."*
>
> ```
> linear type Griff(index into Arena);
> [C001] no lowering: return type       (`-> Griff`)
> [C001] no lowering: parameter type    (`g : Griff`)
> [C001] no lowering: `match` over something other than an `option index into T`
> ```

- [x] ~~**Ein Wort mehr, aber es löst einen WIDERSPRUCH statt eine Lücke zu stopfen.**~~
      **Es ist gar kein Wort** (2026-09-01, `messung/PHASENKONSTRUKT.md` §7). `typedecl`
      schreibt seit jeher `[ "linear" [ "ghost" ] ]` — **das Weglassen von `ghost` IST die
      Unterscheidung**, und die Probe misst `linear type Griff(index into Arena);` mit
      *8 items, 0 errors, 0 hints*. Was fehlt, sind **drei `C001` im Erzeuger**, und *kein
      neues Wort schließt ein `C001`.*
- [ ] **Der Posten gehört unter §31** („Absenkungsabdeckung — alle erzeugten Formen"), nicht
      in eine Liste, die sich gegen die Wortschatzratsche rechtfertigen muss.
- [ ] **Und die Wechselwirkung mit §42 ist ein Aufschlag, kein Rabatt.** Heute ist alles, was
      §42 anfasst, `ghost` und senkt darum nichts ab. Eine Phase an einem `witness` liegt auf
      einem Wert, **der ins C überlebt** — damit trüge die Phasenmaschinerie zum ersten Mal
      eine Absenkungsschuld. *§42 ist billig, weil er unsichtbar ist; §43 macht ihn sichtbar.*

## §44 — Die dritte Stufe für `OA3` · **Zählbarkeit, nicht Sicherheit**

Der binäre Ausstieg — Sprache oder `extern`. **Adas Form (Laufzeitausnahme) passt nicht;
Gabbros passt schon da:** `check` existiert, die Absagedisziplin existiert, die Numerierung
existiert.

> **Eine Pflicht, die statisch nicht fällt, wird eine BENANNTE LAUFZEITABSAGE.** Sie bleibt
> *in* der Sprache, zählt in einer eigenen Liste, und das Zeugnis trägt sie.

**Der Gewinn ist nicht Sicherheit, sondern Zählbarkeit.** Heute ist jeder Ausstieg ein
`extern`, und **`extern` ist ununterscheidbar breit.** Danach gibt es drei Stufen —
*bewiesen · geprüft-zur-Laufzeit · außerhalb* — und **die mittlere fängt genau die Fälle ab,
die heute unnötig ganz nach draußen gehen.**

- [ ] Rechnen, wie viele der heutigen `extern` in die mittlere Stufe fielen. *Ohne die Zahl
      ist es ein Wort ohne gemessenen Bedarf.*

## §45 — EINE Vertrauensliste, nicht drei

*Gemessen 2026-09-01 — heute steht sie an drei Orten, und alle drei sagen dasselbe:*

```
assume-Klauseln in der Quelle          73
C001-Weigerungen des Erzeugers        149
erzeugte Formen ohne Absenkungssatz    64 von 65
```

> *Hier wird geglaubt statt bewiesen* — dreimal, an drei Orten, ohne gemeinsamen Nenner.

**Der Vorschlag ist konzeptuell, nicht syntaktisch: eine Übersetzung erzeugt genau EINE
Vertrauensliste**, und sie enthält alle drei Quellen.

Dann ist *„was muss ich glauben, um diesem Binärcode zu trauen"* **mit einem Befehl
beantwortbar**, und §35s Marke — Annahmen bei Programm n+1 — ist **an einem Artefakt messbar
statt an einem `grep`.**

- [ ] Und das ist der Punkt, an dem **`progress` seinen Platz findet**: eine Umgebungsannahme
      mit Falsifikator gehört in diese Liste, **nicht unter `T6`** (§27, dritte Fundstelle).

## §46 — `platform` und `device` als Annahmeträger

Die Zweiteilung ist gemessen (§36): **sechsmal dieselbe Zeitgeberaussage, weil es keinen Ort
für eine Plattformaussage gibt.** Die Form ist klein:

```gabbro
platform x86_64 { assume … }        device Virtq { assume … }
```

Ein Programm **erbt statt zu kopieren.** *`arch` an `assume` löst sich damit von selbst, weil
der Block es trägt* — und der Posten aus §3/§15/§32 fällt von dieser Seite mit.

- [ ] **Und die Marke wird in EINEM Lauf prüfbar:** eine Plattformannahme in einer
      Programmdatei ist dann **ein Fehler, kein Stilproblem.**

---

## §47 — Was ausdrücklich NICHT vorgeschlagen wird

**Nichts Neues an den Hardwarekonstrukten, bevor die Ratsche steht.**

> Der Wortschatz ist an einem Tag um acht Wörter gewachsen, während der Absenkungssatz bei
> eins blieb — **und drei der fünf Vorschläge oben sind selbst Wörter. Sie müssen sich gegen
> die Ratsche rechtfertigen, sonst ist der Vorschlagende Teil des Problems, das er benannt
> hat.**

Die Reihenfolge folgt daraus und nicht aus dem Reiz:

| | Handel | Wortzahl |
|---|---|---|
| ~~**§42 `phase`**~~ | ~~ersetzt Sonderregeln in vier Bereichen, ein Satz statt vier~~ | ~~**senkt**~~ |
| **§45 Vertrauensliste** | konzeptuell, kein neues Wort | **neutral** |
| **§46 `platform`/`device`** | löst `arch`-an-`assume` mit auf | +2, −1 |
| ~~**§43 `witness`**~~ | ~~löst einen Widerspruch, macht drei Absenkungen trivial~~ | ~~+1~~ |
| **§44 dritte Stufe** | Zählbarkeit — **braucht die Zahl vorher** | +1, ungemessen |

**Die Tafel ist am 2026-09-01 nachgerechnet, und zwei Zeilen sind gefallen**
(`messung/PHASENKONSTRUKT.md`):

| | gerechnet | Wortzahl |
|---|---|---|
| **§42 `phase`** | **NICHT GEBAUT.** Zwei der vier Bereiche haben das Konstrukt schon, einer braucht keines; der Satz ist **null statt null** | **senkt — um EINS**, nicht um vier |
| **§43 `witness`** | **kein Wortschatzposten.** `typedecl` trägt die Unterscheidung schon; es fehlen drei `C001` im Erzeuger | **±0** |

> **Und der Vorschlagende war Teil des Problems, das er benannt hat — nur anders, als §47 es
> befürchtet hat.** Nicht durch acht neue Wörter: durch **vier Zahlen ohne Grundgesamtheit**
> und **eine Trivialitätsbehauptung, deren Widerlegung einen Tag alt im selben Baum lag.**
> *Die Ratsche zählt Wörter; sie zählt keine Messungen, die niemand nachgeschlagen hat.*

---

# TEIL VII — Der Restbeweis unter einem verifizierten Gabbro, und der Weg zur Beta

*Angefügt 2026-09-01, Stand `aecd27f`. **Zwei Fragen, und die erste ist die schärfere:
angenommen Gabbro selbst wäre formal verifiziert — was bliebe dem Nutzer?***

## §48 — Die Antwort ist „ja, plus drei", und die drei sind gemessen

**Was ein verifiziertes Gabbro abnimmt:** die 99 Pflichten wären dann **die richtigen** —
Gabbro garantiert, dass es keine übersieht — und die Absenkung wäre bewiesen: *was der
Prüfer annimmt, führt die Maschine aus.* **Das ist der große Teil, und er ist echt.**

### Was bleibt, gemessen über die 165 sauberen Dateien

```
1  EIGENE LOGIK           99 Pflichten
     postcondition 29 · precondition 23 · preservation 9
     loop invariant 5 · walk invariant 5 · refinement 1
2  HARDWAREANNAHMEN       46 `assume` + 15 device-Pflichten
3  FREMDE RUEMPFE         12 foreign-Pflichten -- und in einem ECHTEN Programm
                          ein Viertel bis ein Drittel aller Funktionen:
                          virtio-net 2/8 · udp-echo 3/10 · zaehlwerk 4/11
4  DIE C-WERKZEUGKETTE     9 `entry`-Verteiler + `cc` + Binder
```

### Punkt 3 ist der, den niemand nennt, und er schrumpft durch keinen Beweiser

`gabbro lean` sagt es über jeden `extern`-Vertrag selbst:

> *„an `ensures` at a body Gabbro never sees: **an ASSUMPTION, not a goal**"*

**Ein verifiziertes Gabbro beweist, dass es den Vertrag richtig VERWENDET — nicht, dass der
Vertrag STIMMT.** Und er wird nicht kleiner, weil jemand einen Beweiser baut. *Er wird
kleiner, indem mehr in Gabbro geschrieben wird.*

- [ ] **Die fünfte Marke, die niemand führt: wie viel Prozent eines echten Kerns steht am
      Ende in Gabbro statt daneben?** Bei `virtio-net` sind es heute **75 %.**

      > **Die Zerlegung gehört DAVOR, und sie ist billiger als die Marke selbst**
      > (Ordner, 2026-09-02). Die 25 % daneben haben drei verschieden teure Gründe:
      >
      > | Kategorie | was sie kostet |
      > |---|---|
      > | Klempnerei | verschwindet nach `B1`/`B2` — **von allein** |
      > | Hardwarebefehle | hängen am C-Ziel, siehe `B5` — **ein Posten, nicht viele** |
      > | was Gabbro nicht ausdrücken kann | **`S2`** — der Posten, den keine Verifikation heilt |
      >
      > **Nur die dritte Kategorie ist eine Aussage über die SPRACHE.** Bestehen die 25 %
      > überwiegend aus den ersten beiden, ist die Marke gut und wird von allein besser. Ist
      > ein Drittel davon Rahmenbedingung, die `spec fn` nicht formulieren kann, misst sie
      > etwas, das keine Bahn schließt. *Eine Zahl, deren Kategorien man nicht kennt, ist
      > `W25` mit einem Prozentzeichen.*

      ---

      **GEMESSEN am 2026-09-02, und die Zerlegung verschiebt die Grenze — zu Gabbros
      Gunsten.** Gegenstand: `messung/treiber/virtio-net.gab` (157 Zeilen ohne Kommentar)
      gegen `../caprock-messbasis/crates/caprock-virtio` (`net.rs` 155, `lib.rs` 347,
      `owned.rs` 122 Zeilen ohne Kommentar). *Gezählt werden FÄHIGKEITEN, nicht Zeilen — ein
      Zeilenverhältnis zwischen zwei Sprachen misst Wortreichtum.*

      **Kategorie B ist kleiner, als der Posten annahm, und zwei Fälle fallen heraus:**

      | | angenommen | gemessen |
      |---|---|---|
      | Speicherordnung (`fence()` vor dem Index) | hängt am C-Ziel | **nein** — `publishes … release` senkt zu `atomic_store_explicit(&AVAIL_IDX, …, memory_order_release)` ab |
      | PCI-Konfigurationsraum (`probe_ecam`) | Port-I/O, hängt am C-Ziel | **nein** — ECAM ist speichereingeblendet, also `at mmio` mit berechneter Basis. Nur ungeschrieben |
      | Legacy-PCI (`0xCF8`/`0xCFC`), `invlpg`/`TLBI`, Shootdown | hängt am C-Ziel | **ja** — und dafür steht `asm` bereit, unverdrahtet (`B5`) |

      > **Die Barriere war der teuerste Posten in B, und sie ist keiner.** C11 drückt
      > Erwerben und Freigeben vollständig aus; über den ganzen sauberen Korpus schreibt der
      > Erzeuger **74 Ordnungsprimitive** (23 `release`, 15 `acquire`, 36 `relaxed`). *Was C
      > nicht kann, ist eine BEFEHLSebene — nicht ein Speichermodell.*

      **Und eine Fehlmessung von mir gehört mit hierher:** mein erster Griff suchte
      `fence|barrier|mfence|sfence|__sync` im erzeugten C, fand null und hätte *„der Treiber
      emittiert keine Barriere"* gebucht. Der Erzeuger schreibt sie als C11-Atomar, und mein
      Muster kannte die Schreibweise nicht. **`W16`, im Zerlegungswerkzeug selbst** — und der
      Grund, dass es auffiel, war, den Rumpf zu LESEN statt die Zahl zu glauben.

      **Was in Kategorie C bleibt, ist nach dieser Messung genau ein Posten:** die
      Eigentumsübergabe. Caprock schreibt `reclaim(buf : Owned<Device>) -> Owned<Driver>`,
      also einen Zustandsübergang eines Besitzrechts. Gabbro hat `own[@marke]` und lineare
      Werte — **aber ob Eigentum ÜBERGEBEN werden darf, fragt bis heute niemand**
      (`R004`/`R007`, und `R013` hat es am 2026-09-02 ausdrücklich stehen lassen).

      *Nicht gemessen:* ob die übrigen Transportfähigkeiten (`poll_used`, `reclaim`, `kick`
      an berechnetem Versatz) in Gabbro schreibbar sind — sie stehen nur nicht in der Datei,
      und **ungeschrieben ist nicht unausdrückbar.** Diese Trennung braucht einen zweiten
      Durchgang, und ohne sie ist die Zahl 75 % weiter ein Quotient ohne Kategorien.

### Punkt 4 fällt — sobald jemand die Teilmenge prüft

**CompCert schließt genau diese Lücke**, und das ist die realistische Antwort. Die Bedingung
ist messbar, **und der Gegenstand liegt seit `09d6c4f` aufgezählt vor: 65 Formen.**

Die Kandidaten, bei denen CompCert zurückhaltend ist — *gezählt im Erzeugnis:*

```
__attribute__   696      volatile      120      restrict      260
_Atomic          39      _Noreturn      20      __asm__         2
__builtin_unreachable 5  _Static_assert  1
```

- [ ] **Die 65 Formen gegen CompCerts Teilmenge halten.** *Eine Messung von Stunden, kein
      Projekt* — und sie entscheidet, ob Punkt 4 ein Posten ist oder eine Fußnote.

**Ein eigener Gabbro-Übersetzer** ist die andere Antwort und **nicht die einfachere**: der
Absenkungssatz zielte dann auf Maschinencode statt auf C. *Es sei denn, er geht durch einen
verifizierten Rücken — dann verschwinden die 64 Formen ohne Satz, weil es keine C-Formen
mehr gibt.*

### Und einer, der keine Beweispflicht ist, sondern eine Sprachgrenze

> **Was nicht sagbar ist, wird durch Verifikation von Gabbro nicht sagbar.** `spec fn` kann
> keine Rahmenbedingung ausdrücken — *„`raeumen` fasst kein anderes Fach an"* ist ein
> Quantor. **Verifiziert man einen Prüfer, der eine Eigenschaft nicht formulieren kann, hat
> man einen verifizierten Prüfer, der sie immer noch nicht formulieren kann.**

### Die ehrliche Fassung

> **Ja — für alles, was in Gabbro geschrieben ist.** Der Nutzer beweist seine Logik und seine
> Hardwareannahmen, **und jede Zeile, die er nicht in Gabbro geschrieben hat, bleibt sein
> Problem.**

---

## §49 — Beta: was fehlt, ausgeplant

*Die Eingangstür ist seit `aecd27f` offen — ein Gabbro-Programm druckt `Hallo`. Damit ist
zum ersten Mal ein Beta-Plan schreibbar, der nicht `N041` misst.*

### B1 — Der Eintritt · **blockiert alles darunter**

```
`int main` im Erzeugnis:  0        `pub fn haupt` braucht einen C-Treiber
```

**Nichts prüft, dass ein `program` genau einen Eintritt hat.** Solange ein Gabbro-Programm
einen handgeschriebenen C-Treiber braucht, um zu laufen, ist die Klempnereifrage `K100` für
den gehosteten Fall mit *nein* beantwortet.

- [x] ~~Ein Eintritt in der Sprache, oder eine benannte Absage mit Grund.~~ **GESCHLOSSEN,
      und am 2026-09-02 von Hand nachgefahren:**

          gabbro new hallo  ->  gabbro build hallo.bau  ->  ./target/hallo/hallo
          Hi                rc=0        im erzeugten C:  int32_t main(void)

      *Kein handgeschriebener C-Treiber.* Damit ist `K100` fuer den gehosteten Fall mit JA
      beantwortet, und der Posten, der alles darunter blockierte, ist weg — **wodurch der
      ungesehene Port zum ersten Mal ueberhaupt moeglich wird.**

### B2 — Zeichenketten · ~~**gemessen unmöglich**~~ **BERICHTIGT: sie gehen HEUTE**

> **Zurückgezogen 2026-09-01, eine Stunde nach dem Schreiben.** Der Satz *„Zeichenketten­ausgabe ist unerreichbar"* stammt aus einem Bahnbericht und ist **hier ungeprüft
> weitergereicht worden.** Gemessen:

```gabbro
type Kette = { bytes : [u8; 64], len : u32 in 0 .. 64, };
extern fn schreib(fd : i32, p : ptr<normal, r> Kette, n : u64) -> i64
    effects { reads p, writes ausgabe } costs <= 8 ops;

$ gabbro pruefe   5 items, 0 errors, 0 hints
$ ./st            Hallo
```

**Eine beliebige Zeichenkette geht, ohne ein neues Wort.** `32-zeichenkette.gab` trägt den
Puffer mit Länge seit dem 2026-08-19, und ein `ptr<normal, r>` darauf bindet an jede
C-Funktion, die man selbst deklariert.

~~**Was NICHT geht, ist eng und benannt:** `puts` und `printf` wollen `const char *`, und
Gabbro hat `u8`. *Das ist eine Signaturfrage an der `extern`-Grenze, keine Typsystemfrage.*~~

> **BERICHTIGT am 2026-09-02, und diesmal war die FRAGE falsch gestellt.** Sie war als
> Signaturfrage gebucht — *„vielleicht reicht, dass `N046` `[u8; N]` gegen `char *`
> durchlässt, wenn der Nutzer es hinschreibt"*. Das ist genau die Buchung, die einen
> Speicherfehler erzeugt:
>
> **`[u8; N]` trägt eine LÄNGE, `const char *` trägt einen ABSCHLUSS.** Das sind zwei
> verschiedene Arten, ein Ende zu markieren, und die Bindung müsste die eine in die andere
> übersetzen. Geht ein `[u8; N]` ohne abschließende Null an `puts`, liest die C-Seite über das
> Ende hinaus — *an der einen Stelle, an der Gabbro keine Schranke mehr hält.*

**Die Regel, und sie folgt aus der Darstellung und nicht aus einem Geschmack:**

> **Gebunden wird, was sein Ende in der SIGNATUR trägt. Nicht gebunden wird, was es in den
> DATEN sucht.**

Der Grund ist nicht, dass die erste Form sicher wäre — `write(1, p, 999)` über 64 Bytes ist
derselbe Fehler, ein Argument weiter. Der Grund ist, dass die Pflicht sich **hinschreiben**
lässt und der Prüfer sie **schon hält**:

| wie der Gerufene das Ende findet | die Pflicht | schreibbar? |
|---|---|---|
| eine ZAHL in der Signatur — `write(fd, p, n)` | `n` darf den Puffer nicht überschreiten | **ja** — `requires n <= KAP`, und `M115` löst es an jeder Rufstelle ein |
| ein ABSCHLUSS in den Daten — `puts(s)` | irgendwo muss eine Null stehen | **nein** — kein Ausdruck über den Parametern beschränkt den Lesevorgang |

*Gemessen:* `error: [M115] `write` requires `n <= 64`, and the argument lies in 999 .. 999`
(`beispiele/gift/633-length-past-the-buffer.gab`). **Eine längennehmende Bindung macht den Ruf
nicht sicher; sie macht die Gefahr AUSSPRECHBAR** — und das ist der ganze Unterschied.

Und dieselbe Regel erklärt `putchar` mit: es nimmt einen WERT, hat kein Ende zu finden und
braucht keine Pflicht. *Drei Sorten, ein Test.*

- [x] **`N052` gebaut** (`cnamen.rs::ABSCHLUSS`, 44 Namen über beide Tafeln, abgeleitet aus den
      Deklarationen mit **vier benannten Ausnahmen**). Er steht VOR `N041`, und die Reihenfolge
      ist das Argument: `N041` weist eine SCHREIBWEISE ab und verschwände an dem Tag, an dem
      Gabbro ein `char` bekäme — `N052` weist eine DARSTELLUNG ab und bliebe stehen.
- [x] **`void *` ist in einem PARAMETER schreibbar, im ERGEBNIS nicht** — und die Asymmetrie
      ist die Regel, nicht die Bequemlichkeit. Herein erzeugt Gabbro Genauigkeit, nach der C
      nicht gefragt hat; hinaus müsste es welche ERFINDEN. Damit sind `write`, `read`,
      `fwrite` und `memcmp` bindbar und `memcpy`, `memmove`, `memset` und `memchr` nicht —
      **alle vier an ihrem Rückgabewert.** Die Tafel wuchs von 138 auf **149 bindbare Zeilen,
      149/149 durch `cc -Wall -Wextra -Werror`.**
- [x] **Das POSIX-Loch geschlossen, soweit gemessen.** `write` band bis heute mit 0 Fehlern und
      einer Deklaration, die der echten WIDERSPRICHT (`int64_t write(int32_t, const Text *,
      uint64_t)` gegen `ssize_t write(int, const void *, size_t)`) — die erzeugte Einheit
      schreibt keinen POSIX-Header, also hatte `cc` nichts zu beanstanden. *Dieselbe Form,
      gegen die `N041` gebaut wurde, eine Namensschicht weiter.* Jetzt steht `<unistd.h>`
      gemessen in `cnamen.rs::POSIX` (47 Zeilen, 13 bindbar), und der Erzeuger schreibt **C's
      eigene Deklaration**.
- [x] **Das zweite Beispiel steht:** `beispiele/64-writes-a-whole-buffer.gab` schreibt einen
      ganzen Puffer mit EINEM `write(fd, p, n)`, gebaut aus einem Manifest, übersetzt unter
      `-Wall -Wextra -Werror`, **gelaufen** — Ausgabe `Puffer\n`, sieben Bytes.
- [ ] **Die Kante der Tafel ist genannt und nicht geschlossen:** `<signal.h>`,
      `<sys/socket.h>` und `<fcntl.h>` liegen außerhalb, und `signal` und `recv` in
      `messung/fragmente/F05.gab` binden bis heute ungeprüft. *Ein Loch mit einem Namen darauf
      ist kein Grün.*
- [ ] **DREI Befunde daneben, und keiner davon ist `B2`** (2026-09-02, gemessen):
      **(1)** an einem Zeigerparameter prüft M1 das Argument GAR NICHT — ein `u32`, ein `bool`
      und ein Zeiger auf den falschen Verbund gehen alle drei mit 0 Fehlern durch;
      **(2)** Gabbro kann auf seinen eigenen Speicher keinen Zeiger bilden (`&x` sagt `M127`
      ab), und ein `static`-Verbund an einem Zeigerparameter geht als WERT hinüber, was `cc`
      zurückweist — *darum trägt `beispiele/64` eine nackte Reihung und die Länge daneben*;
      **(3)** ein `static`-Verbund mit einem Reihungsfeld senkt zu `{ .bytes = 0 }` ab und
      fällt an `-Wmissing-braces`.

**Und der Zustand vorher war schlechter als „ungeprüft", gemessen am 2026-09-02:**

| | |
|---|---|
| Einträge in `cnamen.rs` | **325**, davon **138 mit einer Gabbro-Form** |
| alle 138 | nehmen WERTE (math, ctype, `putchar`, `abort`, `exit`) |
| mit Länge UND Form | **null** |

*Die Regel stand also schon da, unausgesprochen: gebunden war, was einen Wert nimmt.*

### B3 — Der Auffahrtsweg

**Acht Anläufe für „addiere zwei Zahlen"**, von jemandem mit vollem Zugang. Fünf der sieben
Absagen waren Syntaxpapierschnitte.

- [x] ~~`gabbro new` · ein Tutorial · fünf „meintest du"-Hinweise auf genau diese fünf.~~
      **Alle drei stehen** (`12d91a9`). Und die Zahl, gegen die sie gebaut wurden, ist
      gemessen gefallen: **acht Anläufe für „addiere zwei Zahlen" sind EINER** — bei einem
      zweiten Leser, der `midpoint(lo, hi)` über zwei UNbeschränkten `u32` schrieb, was nicht
      im Tutorial steht. *0 Fehler, 0 Hinweise, `slack 0`.*
- [ ] **Und der Test danach ist nicht meiner:** ein zweiter Mensch, oder der ungesehene Port.

### B4 — Die Fläche, die schon steht

```
englische Erstnamen    12 Unterbefehle + 12 FAHNEN, additiv, null von 608 Aufrufstellen
Diagnostik             33 deutsche Meldungen -> 0
SIGPIPE                rc=101 -> 0
zwei Einheiten         `137`, uebersetzt und gelaufen
Bau                    inkrementell nach INHALT, mit Deckungszeile
```

- [x] **Die Fahnen sind englisch, seit dem 2026-09-01** — und es waren **ZWÖLF und nicht
      sechs.** Beide vorhandenen Handgriffe waren zu kurz: `gabbro help` nennt sechs,
      `ERSTNAMEN.md` §5 acht. Vier Fahnen (`--summe`, `--ursprung`, `--sperrrang`, `--eng`)
      werden angenommen und stehen **in gar keiner Hilfe**, und `--je` war eine Wortspaltung
      aus `--je-satz` und `--je-stelle`. *Eine Liste von einem Hilfebildschirm zählt, was
      dokumentiert ist, nicht was angenommen wird.*
- [x] **Ein Wächter erzwingt jetzt den englischen Erstnamen** — für die nächste Fahne UND den
      dreizehnten Unterbefehl: `crates/gabbro-cli/tests/fahnen.rs` liest die **QUELLE**, nicht
      eine Liste, und war rot auf ein eingesetztes `--zaehler` (`exit=101`, Quelle byteweise
      gegen SHA-256 zurückgestellt). *Und er hat beim ersten Lauf zwei Paare gefunden, die die
      handgeführte Liste verloren hatte:* `effects|wirkungen` steht in keiner Tafel, und
      `build|bau` war unter „von Anfang an englisch" abgelegt, obwohl `bau` ein deutscher
      Zweitname ist wie jeder andere.

### B5 — ~~`at port` ist abgesagt~~ **Die Hardwarebefehlsebene liegt außerhalb des C-Ziels**

*Eine abgesagte Absenkung ist ein Loch im Anspruch, kein geschlossener Punkt.*

**Umgebucht am 2026-09-02 auf Verlangen des Ordners, und die Zusammenlegung ist der Punkt:**
`at port` ist ausgeschlossen, weil reines C keine Port-I/O hat. **Dasselbe gilt für `invlpg`,
`TLBI`, `DSB`/`sfence` und den Shootdown — kein einziges davon ist in C ausdrückbar.**

> **Das ist kein Stapel von Einzellöchern, sondern eine Eigenschaft der ZIELWAHL: C11 hat
> eine Ausdrucksdecke, und sie verläuft exakt an der Hardwaregrenze — genau dort, wo Gabbros
> stärkste Konstrukte liegen.** Als ein Posten geführt ist es ein Entwurfsschnitt, den man
> einmal macht; als vier Löcher ist es viermal dieselbe Diskussion.

Gemessen, beide Absagen kommen vom ERZEUGER und nennen dieselbe Ursache:

```
device … at port   C001  „the port space is reached by `in`/`out`, and this generator
                          writes a volatile load at `basis + offset`"
device … at dma    C001  „which barrier a DMA access needs is a statement about the
                          MEMORY MODEL"            (ohne `assume dma_kohaerent`)
```

**Und jetzt der Fund, der die Schätzung halbiert: der Ausstieg EXISTIERT bereits.**
`beispiele/36-asm.gab`:18 schreibt einen x86-Portzugriff, heute, mit `0 errors`:

```gabbro
impl fn ausgeben(tor : u16, wert : u8)
    effects { writes GERAET }   costs <= 1 ops   arch x86_64
    = asm { "outb %[wert], %[tor]" in { wert : "a", tor : "d" } clobbers { memory } };
```

Der Erzeuger senkt das zu `__asm__ __volatile__` ab. **Der `asm`-Rumpf ist ein BENANNTES,
gezähltes Fenster** — mit Wirkungsliste, Kostenschranke, `clobbers` und `arch`-Riegel, genau
das, was `parse.rs` dem Wort `unsafe` entgegenhält: *„there are no unsafe windows; what
touches the machine stands in `axiom`, `raw fn` or `prim fn` — named and counted."*

> **Was fehlt, ist nicht der Ausstieg, sondern seine VERDRAHTUNG.** `device … at port` und
> `asm` stehen beide im Baum, beide richtig, und dass das eine zum anderen absenken könnte,
> gehört zu keinem von beiden — **`OA4` in Reinform**, achte Instanz.

**Und am 2026-09-02 ist die Bedingung erfüllt, unter der der Erzeuger seine eigene Absage
aufheben darf.** Er begründet sie mit Regel A und mit einer Zahl: *„Zero `device … at port` in
426 files."* Das war richtig, solange niemand ein Portgerät schrieb — **jetzt steht eines im
Baum**: `messung/proben/probe-port-nachfrage.gab`, ein 16550 an COM1, dasselbe Gerät, das der
Kommentar in `emit.rs` selbst als Beispiel nennt.

    gabbro pruefe   7 items, 0 errors, 0 hints   (100 % Typdeckung)
    gabbro emit     no lowering: `device … at port`
                    no lowering: a body that carries a `ptr<port, …>`

Samt Wachhund mit Schranke, Fortschrittsannahme (`assume … arch x86_64` mit Falsifikator) und
`on_exceeded`. **Der Prüfer nimmt alles an; nur die Absenkung fehlt** — und die beiden Formen,
die sie bräuchte, stehen beide im Baum.

> *Regel A hat zwei Hälften, und die zweite wird seltener zitiert: **kein Konstrukt ohne
> gemessene Nachfrage — und keine Weigerung ohne gemessenen Mangel.** Die Nachfrage ist
> hiermit gemessen.*

*Nebenbei ist das die ehrlichste Antwort auf „Gabbro ohne `unsafe`": es stimmt in der
Sprache, und die Stelle, an der es nicht mehr stimmt, ist nicht Gabbros Entwurf, sondern das
Ziel.*

### B6 — Und die zwei Entscheidungen beim Ordner

- [ ] **`H = 4`** — alle vier hängen an Programmen, die Gabbro nicht annimmt, jede Absage
      nachgemessen. *Sieben von zehn buchen, oder den vier eine eigene Spalte.*
- [ ] **`state`** — nicht bauen, aber die Absage um genau zwei Zeilen ergänzen. **Der einzige
      rote Wächter seit drei Tagen.**

---

## §50 — Die Reihenfolge, und sie folgt aus §48

| # | | warum hier |
|---|---|---|
| **1** | **B1 Eintritt** | blockiert jeden Lernbarkeitstest und `K100` |
| ~~**2**~~ | ~~**Die 65 Formen gegen CompCert**~~ | **AUS DEM BETA-PFAD GENOMMEN, Ordner, 2026-09-02.** Der Posten bleibt richtig und bleibt stehen — er gehört nur nicht vor `0.1.0`. *Eine Beta braucht einen Prüfer, der nicht lügt, keinen verifizierten Übersetzer;* der Satz stand schon in §50s eigener Schlussbemerkung und wurde von der Reihenfolge darüber nicht eingelöst. **−4 bis −6 h vom Restweg** |
| **3** | **Der ungesehene Port** | ~~die einzige Messung, die die Liste umschreiben kann~~ **— und die Begründung gehört schärfer, Ordner 2026-09-02:** *er ist nicht nur die einzige Messung, die schlecht ausgehen kann; er ist die einzige, deren Ausgang **die Beta-Liste selbst neu bewertet.*** Scheitert ein fremder Schreiber an Formen, die dieser Korpus nie gebraucht hat, dann sind Stunden dieser Liste **an der falschen Stelle investiert**. Daraus folgt die Reihenfolge: eine halbtägige Aufräumrunde davor ist richtig — *sie räumt, ohne Annahmen zu zementieren* — und **alles Größere danach ist falsch, bis das Ergebnis da ist** |
| **4** | B2 Zeichenketten | mit der Ratschenrechnung davor |
| **5** | B3 Auffahrtsweg | erst sinnvoll, wenn B1 und B2 stehen |
| **6** | Die fünfte Marke (§48) | *wie viel Prozent stehen in Gabbro* — heute 75 % bei einem Treiber |

**Und was NICHT auf dieser Liste steht, gehört ausgesprochen:** die Beweisseite. `145 von 381
Rümpfen`, `1 Absenkungssatz von 65`, die Naht zwischen zwei Beweisern, die in keiner Logik
existiert. *Eine Beta braucht keinen Beweis — sie braucht einen Prüfer, der nicht lügt. Aber
der Satz, dass ein verifiziertes Gabbro dem Nutzer die Arbeit abnimmt, hängt an ihr.*

---

# TEIL VIII — Die Sprache selbst, und zwei Auslieferungswege

*Angefügt 2026-09-01 auf `2110702`. **Teil VII beantwortete, was für eine Beta fehlt. Dieser
Teil trennt davon, was an der SPRACHE offen ist** — nicht am Werkzeug, nicht am Beweis, nicht
am Prozess.*

## §51 — Was an der Sprache offen ist, nach Gewicht

### S1 — Domänen sind geschlossen · **der schärfste Widerspruch zum Ziel**

Siebzehn Wörter, keine benutzerdefinierten. **Eine neue Datenstruktur braucht den
Sprachautor.** Gerechnet, nicht gebaut: die Regel senkt **drei** Wörter, nicht siebzehn —
*und trägt trotzdem, weil `domaenenschranke` wenige Aufrufer hat* — **ZWEI, nachgezählt 2026-09-01**, nicht einen: `kosten.rs`:665 und `m1.rs`:3824. *Die Kopfzeile von `domaene.rs` sagt es seit dem 2026-08-19 selbst, und die Zahl daneben war eine Jahreszahl.* Ohne `costs`-Zeile
fragt niemand nach der Schranke einer Domäne, und `reach … via` steht seit jeher in der
Grammatik.

- [ ] Der billigste offene Sprachposten mit echtem Ertrag. *Nicht Wortschatz, sondern
      **Schranke**: von „wird gefragt" nach „steht fest".*

### S2 — `spec fn` kann keine Rahmenbedingung ausdrücken

> *„`raeumen` fasst kein anderes Fach an"* ist ein **Quantor**, und Rahmenbedingungen sind
> der häufigste Inhalt einer Kernspezifikation. **Dafür verlässt der Nutzer heute die
> Sprache.**

Und das ist der eine Posten, den Verifikation nicht heilt: *verifiziert man einen Prüfer, der
eine Eigenschaft nicht formulieren kann, hat man einen verifizierten Prüfer, der sie immer
noch nicht formulieren kann.*

### S3 — `char` an der `extern`-Grenze

Beliebige Zeichenketten gehen **heute** (`ptr<normal, r>` auf einen Puffer mit Länge). Was
nicht geht: `puts`/`printf` wollen `const char *`, Gabbro hat `u8`.

> **Eine Signaturfrage an der `extern`-Grenze, keine Typsystemfrage.** `N046` ist der Pass,
> der sie stellt.

- [ ] Rechnen, ob `N046` `[u8; N]` gegen `char *` durchlassen soll, wenn der Nutzer es
      hinschreibt. *Kein Wort in der Sprache.*

### S4 — Der Ausstieg ist binär

Sprache oder `extern`. Ada hat einen Abstiegspfad; **Gabbros Form läge schon da** — `check`
existiert, die Absagedisziplin existiert.

> Eine Pflicht, die statisch nicht fällt, wird eine **benannte Laufzeitabsage** statt eines
> `extern`. **Der Gewinn ist Zählbarkeit, nicht Sicherheit** — heute ist jeder Ausstieg ein
> `extern`, und `extern` ist ununterscheidbar breit.

- [ ] **Braucht die Zahl vorher:** wie viele der heutigen `extern` fielen in die mittlere
      Stufe? *Ohne sie ein Wort ohne gemessenen Bedarf.*

### S5 — Zwei kleine, beide gemessen

```
`let x = if b { a } else { 0 };`   error: [P002] `if` is a word of the vocabulary,
                                                not an identifier
`type W = u32 wrapping;`           error: [P001] `;` expected, `wrapping` found
```

`if` als Ausdruck: **der Erzeuger schreibt `?:` selbst** (8 Stellen), die Sprache kann es
nicht. `wrapping` am Typalias: `reg`- und Slotfelder tragen es, ein `type` nicht — *für
Bitcode, wo jede Rechnung umlaufen SOLL, eine unnötige Asymmetrie.*

### S6 — `at port` ist abgesagt, nicht gelöst

*Eine abgesagte Absenkung ist ein Loch im Anspruch, kein geschlossener Punkt.* Solange
Portzugriffe außerhalb der Sprache stattfinden, gilt „MMIO gelöst" **für memory-mapped und
nicht für x86-I/O.**

### S7 — RMW auf ein Gerät hat keine Atomarität

`R012` nimmt nur Fälle weg, die **auch ohne Unterbrechung** falsch sind. Ein `modify`, das
W1C- und geteilte Register unterscheidet, wäre die Fortsetzung der Phasenklasse — *und
§42 hat gezeigt, dass diese Familie teurer ist, als sie aussieht.*

### S8 — The three layers of the page table · **all three moved on 2026-09-01**

*The old entry read: TLB (no construct names `invlpg`/`TLBI`/shootdown, cheap and really
exploitable) · preservation (as an induction it needs no quantification) · self-reference
(unsolved, seL4 too). **Measured against Caprock, two of those three were wrong and the third
was booked in the wrong form.*** `§5` carries it in full; the short version:

| | |
|---|---|
| **TLB** | The construct has a **witness**, not a demand: 51 page-table entry writes in Caprock, and its IOMMU half already routes every one of them through a hand-written `write_entry` that *"never returns without a flush"*. But **the rule belongs at the KIND of change**: all 6 change/remove functions invalidate, and 7 of 13 ADD functions deliberately do not. The architectural half is now `assume neuer_eintrag_verdraengt_nichts arch x86_64`. |
| **Preservation** | The induction **breaks on the permission hierarchy** — one interior `RW` bit moves up to 512³ leaves the write never touched — *and whether it breaks at all depends on what `m.schreibbar` means, which nothing in this tree decides.* The way out (induction over PATHS) is blocked twice: `D018` refuses `ancestors of` over a `walk`, and the bound behind it is silent. **Do not build across that coupling.** |
| **Self-reference** | **Nothing in Caprock writes it down**, not even as a comment. Booked as `assume kern_bleibt_unter_jeder_aenderung_abgebildet … falsifier sonde_kern_entmappt`, because its load-bearing clause is about a TRACE and no `ensures` can say it. |

**And the general rule this section paid for twice** (`W29`): *before a rule over a word
belongs a count of its uses — and not only how many, but whether they go wrong in the SAME
DIRECTION.* Over `walk`: two page tables, one **inode block tree**, two grammar probes. Over
a PTE write: four kinds, and a rule at the write would be redundant for one and wrong for
another. **Two uses that mask each other are worse than ten that do the same thing.**

### Und was NICHT mehr offen ist

```
`~` · `u32::max` im Ausdruck · `w1c` als Zugriffsklasse       zu, `ff9d29a`
Vorrang der Bitoperatoren                                     zu, `d8c79d1`
Zeichenketten IM Programm                                     gingen die ganze Zeit
Parametrizitaet                                               gemessen erledigt: 5 Skelette mehrfach
ein gehosteter Eintritt                                       zu, `2110702`, OHNE neues Wort
```

---

## §52 — Auslieferung: AUR-Paket · **die Vorbedingung steht, und der Weg ist GEMESSEN**

*Der Befund, der es billig macht, ist gemessen — und am 2026-09-01 nachgemessen statt zitiert:*

```
Abhaengigkeiten der drei Kisten:   NULL externe   `cargo tree`: drei Pfadkisten, sonst nichts
version                            0.0.1          git tag       1  (war 0)
```

**Der Tag `0.0.1` steht seit dem 2026-09-01 auf `b05a6fd`** — annotiert, mit dem
Freigabeschema im Text, **und NICHT gepusht**: das entscheidet der Ordner. *Damit ist der
Punkt, der „die eigentliche Arbeit" hieß, erledigt, und §52 ist von einer Vorbedingung auf
eine Rechnung geschrumpft.*

### Der ganze Weg, einmal gefahren

**Nicht überschlagen, sondern durchlaufen** — Archiv aus dem Tag, ausgepackt, `--frozen
--offline` gebaut, Binärprogramm über den Korpus gefahren:

| Schritt | gemessen |
|---|---|
| `git archive --prefix=Gabbro-0.0.1/ 0.0.1` | **3 293 628 Byte**, 925 Einträge |
| `cargo build --frozen --release --offline` | **10,65 s** |
| `target/release/gabbro` | **5 117 496 Byte** (4,9 MiB) |
| `gabbro check beispiele/01-tabelle.gab` | läuft, `0 errors` |

**`--offline` und `--frozen` gehen, weil `Cargo.lock` 352 Byte hat und keine Registry nennt.**
*Das ist der eigentliche Grund, warum dieses Paket billig ist: kein `cargo fetch` im
`prepare()`, keine Netzstufe, keine Lieferkette, die jemand prüfen müsste.*

### Was in den `PKGBUILD` gehört — jede Zeile mit ihrem Beleg

```
pkgname=gabbro
pkgver=0.0.1
arch=('x86_64')
url='https://github.com/SimonVitzethum/Gabbro'
license=('AGPL-3.0-only')                # Cargo.toml; die Zusatzerlaubnis ist KEIN SPDX-Ausdruck
depends=('gcc')                          # LAUFZEIT: `cc` fuer `gabbro build`
makedepends=('rust')                     # >= 1.86 -- `f64::next_up`/`next_down`
source=("$pkgname-$pkgver.tar.gz::$url/archive/refs/tags/$pkgver.tar.gz")
build()   { cd "Gabbro-$pkgver"; cargo build --frozen --release --offline; }
check()   { cd "Gabbro-$pkgver"; cargo test  --frozen --offline --no-fail-fast; }
package() { install -Dm755 "Gabbro-$pkgver/target/release/gabbro" "$pkgdir/usr/bin/gabbro"
            install -Dm644 "Gabbro-$pkgver/LICENSE"          "$pkgdir/usr/share/licenses/$pkgname/LICENSE"
            install -Dm644 "Gabbro-$pkgver/LIZENZ-ZUSATZ.md" "$pkgdir/usr/share/licenses/$pkgname/LIZENZ-ZUSATZ.md" }
```

* **`depends=('gcc')`, und das ist nachgeschlagen und nicht geraten:** `pacman -Qo
  /usr/bin/cc` nennt `gcc`. Gebraucht wird es **allein von `gabbro build`** — `bau.rs`:742
  und :763 sind die *einzigen* zwei `Command::new` im ganzen Baum. `check`, `emit`, `abi`,
  `costs`, `effects`, `obligations`, `certificate` und `lean` lesen und schreiben Dateien.
* **`ldd` auf dem gebauten Programm: `libgcc_s`, `libc`, sonst nichts.** Kein `gcc-libs` von
  Hand — namcap zieht es aus genau dieser Liste.
* **`LIZENZ-ZUSATZ.md` muss mit ins Paket.** `AGPL-3.0-only` steht in Archs
  `/usr/share/licenses/common`, die **Zusatzerlaubnis nach AGPL §7 aber nirgends** — und sie
  ist die Hälfte, die den Nutzer betrifft. *Ein Paket, das nur den SPDX-Ausdruck mitliefert,
  liefert die halbe Lizenz.*
* **Isabelle und Lean gehören NICHT hinein**, in keiner der drei Listen. Sie prüfen den
  **Baum**, nicht das **Erzeugnis** — `beweise/` und `programmlogik/` fahren hier und nicht
  beim Nutzer. *Ein `makedepends` auf einen Beweiser wäre die Aussage, ein Paket sei ohne ihn
  nicht baubar, und sie wäre falsch.*
* **`check()` braucht kein `gcc` über `base-devel` hinaus.** `cargo` braucht ohnehin einen
  Binder, und `base-devel` ist bei `makepkg` gesetzt; die Proben selbst rufen keinen
  C-Übersetzer (`eintritt.rs`:247 sagt es wörtlich: *„no C, no compiler, no linker"*).

### Und die Prüfsumme ist der eine Posten, der offen BLEIBT

*Die `sha256` meines Archivs ist `a0f3da02…` — **und sie ist für den `PKGBUILD` wertlos.***
`git archive` und GitHubs Tarball sind nicht byteidentisch: Kompressionsstufe und Zeitstempel
gehören dem Erzeuger, nicht dem Baum. **Die Zahl, die in den `PKGBUILD` gehört, kann erst
gemessen werden, wenn der Tag GEPUSHT ist** — und das entscheidet der Ordner.

> *Dieselbe Klasse wie `W16`: eine Prüfsumme über das falsche Artefakt sieht aus wie eine
> Prüfsumme.*

- [x] **Version und Tag** — `0.0.1`, annotiert, auf `b05a6fd`, ungepusht.
- [x] `depends` / `makedepends` gerechnet, jede Zeile mit Beleg.
- [ ] **Die Prüfsumme über das Freigabearchiv** — hängt am Push, nicht an dieser Bahn.
- [ ] **`aur/`-Dateien liegen NICHT in diesem Baum**, und das ist eine Entscheidung: ein
      `PKGBUILD` gehört ins AUR-Repositorium, nicht neben den Übersetzer. *Er stünde hier als
      zweites Register über dieselbe Sache.*

*Aufwand: die Bahn ist gefahren; was bleibt, ist der Push und fünfzehn Zeilen abtippen.*

---

## §53 — Auslieferung: WASM und eine VS-Code-Erweiterung

**Gemessen 2026-09-01, und es geht heute:**

```
$ cargo build --target wasm32-wasip1 -p gabbro-cli --release
  Finished `release` profile in 11,50s
  target/wasm32-wasip1/release/gabbro.wasm    3 152 325 Byte  (3,0 MiB)
```

> **Nachgemessen am selben Tag auf `b05a6fd`, aus sauberem Zielverzeichnis: 9,67 s und
> 3 165 896 Byte.** Die Zeit ist eine andere Maschine, aber **die 13 571 Byte sind es nicht** —
> sie sind sechzehn Commits. *Die obere Zahl trägt `2110702` als Handgriff und nicht nur ein
> Datum, und das ist der Unterschied zwischen einer Messung und einer Jahreszahl.*

**Null Abhängigkeiten, `unsafe_code = forbid`, kein Systemruf außer Datei-Ein/Ausgabe** —
das ist der Grund, warum es beim ersten Versuch durchläuft.

### Was in WASM geht und was nicht — die Trennung ist scharf

| | |
|---|---|
| **geht** | `check` · `emit` · `abi` · `costs` · `effects` · `obligations` · `certificate` · `lean` — **alles, was liest und schreibt** |
| **geht NICHT** | `build`. `bau.rs:742` und `:763` rufen `std::process::Command` für `cc` und den Binder. *In WASM gibt es keinen Kindprozess.* |

- [ ] **Und das ist keine Einschränkung, sondern die richtige Trennung:** eine Erweiterung
      soll prüfen und Diagnostik zeigen, nicht binden. `build` bleibt beim lokalen
      Binärprogramm.

### Die Erweiterung, in drei Stufen

**Stufe 1 — Diagnostik ohne LSP.** Die Erweiterung ruft `gabbro.wasm check` bei jedem
Speichern und übersetzt die Ausgabe in `Diagnostic`s. **Das Format liegt schon dafür bereit:**

```
error: [M101] datei.gab:2:12: the return value requires `u32`, …
    2 |     return a + b;
      |            ^^^^^
      = M1: every operation must stay inside the range of its result type
```

*Kennung, Datei, Zeile, Spalte, Spanne, Erklärung — eine Zeile Regex je Feld.* **Und die
Fußzeile `Not checked in this run: 9 passes CARRIED` gehört in die Statusleiste, nicht
weggeworfen** — sie ist das, was Gabbro von anderen Übersetzern unterscheidet.

**Stufe 2 — Syntaxhervorhebung.** 221 Wörter, und **die Liste ist maschinenlesbar**
(`kw.rs`, geratscht). *Eine TextMate-Grammatik aus `zaehle-wortschatz.py` zu erzeugen ist
richtiger, als sie zu schreiben* — dann kann sie nicht veralten.

**Stufe 3 — was Gabbro kann und andere nicht.** `gabbro costs` druckt `computed / promised /
slack` je Rumpf. **Das gehört als Inlay-Hinweis an die `costs`-Zeile** — der Nutzer sieht,
dass sein Rumpf 48 von 64 zugesagten Ops braucht, ohne einen Befehl zu tippen. *Dasselbe für
`gabbro effects --vergleich`: zu weit deklarierte Wirkungen als schwacher Hinweis.*

- [ ] **Reihenfolge: Stufe 1 zuerst und allein.** Sie ist die Eingangstür für einen zweiten
      Menschen, und sie braucht kein LSP.
- [ ] Kein `wasm-bindgen`, kein `wasm-pack`: **`wasip1` läuft in VS Code über
      `@vscode/wasm-wasi`**, und die Abhängigkeitsfreiheit bleibt erhalten.
- [ ] *Ungemessen: kein WASM-Laufzeitsystem auf diesem Rechner. Die 3,0 MiB sind gebaut, aber
      NICHT gelaufen* — `wasmtime` fehlt, und das gehört gemessen, bevor jemand die
      Erweiterung schreibt.

---

## §54 — Reihenfolge für Teil VIII

| # | | warum |
|---|---|---|
| **1** | **`gabbro.wasm` einmal LAUFEN lassen** | 3,0 MiB gebaut und nie ausgeführt. *Eine Messung von Minuten, und sie trägt §53 ganz* |
| ~~**2**~~ | ~~Freigabe: Version + Tag~~ | **erledigt 2026-09-01**: `0.0.1` annotiert auf `b05a6fd`, ungepusht |
| ~~**3**~~ | ~~AUR-`PKGBUILD`~~ | **gerechnet 2026-09-01** (§52), der ganze Weg einmal gefahren. Offen bleibt allein die Prüfsumme, und die hängt am Push |
| **4** | Erweiterung Stufe 1 | die Eingangstür für einen zweiten Menschen |
| **5** | **S1 Domänenregel** | der billigste Sprachposten mit echtem Ertrag |
| **6** | S3 `char` an der Grenze · S5 die zwei kleinen | je eine Rechnung gegen die Ratsche |
| **7** | S2 · S4 · S6 · S7 · S8 | Forschungs- und Entwurfsanteil |
