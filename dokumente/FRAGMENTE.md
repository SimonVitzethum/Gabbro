# Gabbro — die ausgeschriebenen Fragmente

**Sechs Fragmente aus sechs Caprock-Bereichen, gegen die Grammatik von heute gehalten.**
Stand 2026-08-14. **Kein Uebersetzer liest das.** Nichts davon ist uebersetzt, gelaufen oder
gemessen — es ist Text, der gegen [`SYNTAX.md`](SYNTAX.md) geprueft wurde, Produktion fuer
Produktion.

Bis heute stand in `SYNTAX.md` unter den offenen Punkten: *„Kein einziges ausgeschriebenes Fragment
liegt im Ordner."* Die Fragmente lagen im Scratchpad zweier frueherer Sitzungen und waren gegen
**aeltere** Fassungen der Grammatik geschrieben. Diese Datei holt sie herein, zieht sie nach und
faellt je Fragment ein Urteil.

## Was sich seither geaendert hat — und was das an den Fragmenten bewegt hat

| Aenderung | Wirkung auf die Fragmente |
|---|---|
| *„keeping"* ist weg, `mirrors <reg> from <reg>;` einmal je Geraet | **schliesst** die teuerste Luecke des VT-d-Fragments (Falle 4) |
| `publishes` ist Pflicht, `publishes nothing` gibt es | **schliesst** zwei der drei Befunde des Pruefgeruest-Fragments |
| `relaxed` gibt es | **schliesst** den dritten |
| `old`, `offset_into`, `never` sind echte Produktionen | `old(...)` in `delete_leaf` traegt jetzt |
| `loop … variant` ist weg; `traverse`/`retry`/`forever` | `retry` traegt den virtio-Poll unveraendert; `forever` traegt die Dienstschleife **nicht** (kein Ausgang) |
| `costs` zaehlt Operationen, nicht Zyklen | alle `costs`-Zeilen umgestellt — und `SYNTAX.md` selbst nicht (**«B4»**) |
| `bitpos` als Bereich `@[33:24]`, `bank … at expr` | **schliesst** die drei groessten VT-d-Luecken (Mehrbitfelder, laufzeitberechnete Registerlage) |

**Der Ertrag ist unsymmetrisch, und das ist die Nachricht:** die Geraeteseite hat sich in den
letzten zwei Fassungen deutlich geschlossen, die **Ausdrucks**seite nicht. Von den 31 Befunden
unten sitzen 7 in `SYNTAX.md` selbst (Widersprueche zwischen Prosa, Beispiel und EBNF), und der
schwerste davon (**«B2»**) macht **jedes Atomic, jede Sperre und jeden kritischen Abschnitt in
allen sechs Fragmenten unschreibbar** — nicht weil die Konstrukte fehlen, sondern weil sie in der
EBNF **nicht erreichbar** sind.

## Wie geprueft wurde

1. **Wortschatz:** jedes Wort, das kein Bezeichner ist, muss in der geschlossenen Tabelle
   (`SYNTAX.md` §Wortschatz) stehen. Einheiten hinter `costs`/`bounded` sind freie Bezeichner —
   deshalb kann kein Waechter sehen, ob dort `ops` oder `cycles` steht (**«B4»**).
2. **EBNF:** jede Zeile gegen ihre Produktion, mit Zeilennummer in `SYNTAX.md`.
3. **Erreichbarkeit:** maschinell nachgerechnet, welche der 103 Regeln von `program` aus erreichbar
   sind. Ergebnis: **drei tragende Regeln sind es nicht** (`atomicdecl`, `lockdecl`, `lockstmt`),
   dazu die zwei lexikalischen (`comment`, `newline`), die es sein duerfen. `pruefe-syntax.sh`
   prueft **Geschlossenheit** (kein benutztes Nichtterminal ohne Definition) — die Gegenrichtung,
   **Erreichbarkeit**, prueft er nicht, und genau dort sass der Fund.
4. **Was nicht schreibbar ist, steht als Kommentar `-- «Bnn»` in der Zeile** statt glattgezogen zu
   werden. Ein Fragment, das nur deshalb durchgeht, weil die unbequeme Zeile fehlt, ist kein
   Ergebnis.

## Bilanz

| | |
|---|---|
| Fragmente | **6** aus 6 Bereichen (Cap-Space · VT-d · IPC · Treiber · Userspace · Pruefgeruest) |
| **passt unveraendert** | **0** |
| **passt mit Befund** | **4** (F1 Cap-Space, F2 VT-d, F4 Treiber, F6 Pruefgeruest) |
| **passt nicht** | **2** (F3 IPC-Fastpath, F5 Dienstschleife) — beide scheitern an einer *tragenden* Aussage, nicht an Beiwerk |
| Befunde | **31**, davon **7** in `SYNTAX.md` selbst |
| Befunde, die eine namentlich *bezahlte* Caprock-Falle wieder aufmachen | **5**: B11 (D0, namenloser Austritt) · B18 (wiederverwendete Virtqueue) · B19 (arch-neutrale Barriere) · B21 (der Zaehler, der nur waechst) · B26 (abweisen statt deuten) |

**Die zwei „passt nicht" sind der Ertrag dieser Runde.** F3 scheitert daran, dass ein `transition`
**genau einen** Ort schreibt — die Antwortpflicht (`caller` und `reply_owner` gemeinsam) war der
Grund, aus dem das Fragment ueberhaupt in `state`-Form geschrieben wurde. F5 scheitert daran, dass
`forever` **keinen Ausgang** hat: die D0-Lehre („ein namenloser Austritt aus der Serverschleife hat
zehn Tage gekostet") ist in der Grammatik von heute nicht ausdrueckbar, weil es ueberhaupt keinen
Austritt gibt.

---

# F1 — Cap-Space: `delete_leaf`, `unlink`, `revoke`

**Herkunft (Rust-Original):** `crates/caprock-cap/src/space.rs:1062` (`delete_leaf`), `:1044`
(`unlink`), `:991` (`release_slot`), `:619` (`revoke`); `crates/caprock-cap/src/object.rs`
(`ObjectKind`).
**Vorlage im Scratchpad:** `delete_leaf.gabbro` (138 Z.), `syntax-entwurf.md:1063-1243`.

**Nachgezogen:** `module x;` → `module x { … }` (`moduledecl` verlangt Klammern, SYNTAX.md:113) ·
`use a::{b,c}` → drei `usedecl` (:114 kennt keine Klammerliste) · `held(CAPS)` → `Held(CAPS)`
(§2 fuehrt `linear ghost type Held(Lock)`) · `costs <= 200 cycles` → `<= 200 ops` · `type Gen = u32
wrapping;` entfaellt, `wrapping` gehoert an den Slot (:388) · zweite Tabelle `objects { … }` **im**
`table` → eigene `table CapObjects` mit `index into CapObjects` · Slotfelder mit Schlusskomma
(:386) · `tagged ObjectKind : u8 { … }` → `tagged type … = { … }` (:147) · `invariant` mit `cost`
und `runs` (:389, war vorher weggelassen).

```gabbro
module caprock::cap::space {

use caprock::mem::Rights;
use caprock::mem::Region;
use caprock::sched::ThreadId;

const NSLOTS   : u32 = 80256;
const NOBJECTS : u32 = 4096;

type SlotIdx  = u32 in 0 ..< NSLOTS;
type Refcount = u32 in 0 ..< NSLOTS;

opaque type Badge   = u64;
opaque type EpId    = u32;
opaque type PdId    = u16;
opaque type Pa      = u64;
opaque type ByteLen = u64;

reason CapError {
    NoSlot      = 1 "kein freier Capability-Slot mehr"
    NoObject    = 2 "kein freier Objekt-Eintrag mehr"
    Invalid     = 3 "ungueltiges oder abgelaufenes Handle"
    HasChildren = 4 "Operation auf einem Cap mit Kindern, erst revoke"
    Unaligned   = 5 "Region verletzt die Granularitaetsbedingung"
    TooSmall    = 6 "Region zu klein fuer die Zusicherung, die die Cap traegt"
    exhaustive
}

-- «B15» `variants` (SYNTAX.md:147) nimmt je Variante GENAU EINEN typeexpr. Wo Rust eine
-- Felderliste inline schreibt, braucht Gabbro einen benannten Verbund. Fuenf davon.
type SchedParams = { budget : u32, period : u32, };
type ReplyRef    = { ep : EpId, caller : ThreadId, };
type MmioRange   = { phys : Pa, len : ByteLen, };
type DmaRef      = { phys : Pa, len : ByteLen, dir : DmaDir, coherence : DmaCoherence, };
type HandlerRef  = { ep : EpId, pd : PdId, sidecar : Pa, len : ByteLen, };

tagged type ObjectKind = { Memory(Region), Endpoint(EpId), Notification(EpId),
                           Tcb(ThreadId), SchedContext(SchedParams), Reply(ReplyRef),
                           PdControl(PdId), Loader(u32), Mmio(MmioRange), Irq(u32),
                           Dma(DmaRef), SyscallHandler(HandlerRef), FaultHandler(HandlerRef) };

-- «B2» `lockdecl` (SYNTAX.md:471) ist von `program` aus NICHT ERREICHBAR: `item` (:111-112)
-- fuehrt es nicht auf. Dieselben zwei Zeilen stehen als Beispiel in §11 der Datei, die sie
-- ausschliesst. Betroffen: jede Sperre in allen sechs Fragmenten.
lock CAPS protects { plaetze, cdt } rank 0 masks irqs;
lock MEM  protects { freelist }   rank 9;

-- «B16» Zwei Tabellen, weil `table` genau EIN `slot`-Wort kennt (:385-386). Der Cap-Space hat
-- Slots UND Objekte; `index into CapObjects` traegt die Verbindung, aber keine Invariante
-- kann sie noch aussprechen, s. B13 weiter unten.
table CapObjects count NOBJECTS {
    slot {
        used     : bool,
        gen      : u32 wrapping,
        kind     : ObjectKind,
        refcount : Refcount,
    }
}

table CapSpace count NSLOTS {
    slot {
        used         : bool,
        gen          : u32 wrapping,
        object       : index into CapObjects,
        rights       : Rights,
        badge        : Badge,
        parent       : option index into CapSpace,
        first_child  : option index into CapSpace,
        next_sibling : option index into CapSpace,
        prev_sibling : option index into CapSpace,
    }

    -- «B16» Das `pred` einer `invariant` braucht ein `place` fuer die Tabelle
    -- (`slots of place`, :239) — die Grammatik bindet aber im `table`-Rumpf keinen Namen.
    -- `Self` ist hier GERATEN; §2 fuehrt `Self` nur als eingebautes Wort ohne Bindungsregel.
    invariant wurzel_ohne_vorgaenger cost O(n) runs offline :
        forall s in slots of Self :
            Self.slots[s].parent == None => Self.slots[s].prev_sibling == None;

    -- «B14» Die beiden Gegenseitigkeits-Invarianten brauchen die AUFLOESUNG eines
    -- `option index into` im Praedikat (`slots[s.next_sibling].prev_sibling == s`).
    -- `match` loest das in einer Anweisung auf, im Praedikat gibt es dafuer nichts.
    -- «B13» `refcount_matches` braucht eine Zaehlung ueber eine ZWEITE Tabelle
    -- (`o.refcount == count(s in slots: s.object == o)`). `pred` (:230-247) kennt keine
    -- Aggregation und keine tabellenuebergreifende Domaene. Der Kern der Buchfuehrung des
    -- Faehigkeitssystems ist damit nicht formulierbar — das ist der teuerste Befund an F1.
}

-- «B1» Diese Form — `spec fn … = pred;` — benutzt SYNTAX.md:287 selbst. `fndecl` (:266-274)
-- laesst als Rumpf nur `block | ";"`. Ueber einen `block` ist ein Quantor NICHT erreichbar:
-- `return` nimmt `expr`, und `pred` haengt nirgends unter `expr`. Ohne diese Produktion ist
-- in allen sechs Fragmenten keine einzige `spec fn` schreibbar.
spec fn ist_blatt(c : ptr<normal, r> CapSpace, s : SlotIdx) -> bool
    effects { pure }
    = c.slots[s].used && c.slots[s].first_child == None;

spec fn cdt_wohlgeformt(c : ptr<normal, r> CapSpace) -> bool
    effects { pure }
    = forall s in slots of c : c.slots[s] reaches WURZEL via parent;

impl fn unlink(c : ptr<normal, rw> CapSpace, s : SlotIdx)
    requires  Held(CAPS), c.slots[s].used
    ensures   c.slots[s].parent == None,
              c.slots[s].prev_sibling == None,
              c.slots[s].next_sibling == None
    maintains cdt_wohlgeformt
    effects   { writes c.slots, locks CAPS }
    costs     <= 40 ops
{
    match c.slots[s].prev_sibling {
        Some(p) => { c.slots[p].next_sibling = c.slots[s].next_sibling; }
        None    => {
            match c.slots[s].parent {
                Some(par) => { c.slots[par].first_child = c.slots[s].next_sibling; }
                None      => { }
            }
        }
    }
    match c.slots[s].next_sibling {
        Some(n) => { c.slots[n].prev_sibling = c.slots[s].prev_sibling; }
        None    => { }
    }
    c.slots[s].parent       = None;
    c.slots[s].first_child  = None;
    c.slots[s].next_sibling = None;
    c.slots[s].prev_sibling = None;
}

impl fn release_slot(c : ptr<normal, rw> CapSpace, s : SlotIdx)
    requires  Held(CAPS)
    ensures   !c.slots[s].used
    effects   { writes c.slots, locks CAPS }
    costs     <= 20 ops
{
    c.slots[s].gen  += 1;
    c.slots[s].used  = false;
    c.slots[s].badge = 0;
}

impl fn delete_leaf(c  : ptr<normal, rw> CapSpace,
                    o  : ptr<normal, rw> CapObjects,
                    a  : ptr<normal, rw+own> PhysAllocator,
                    rf : ptr<normal, rw+own> Finalized,
                    s  : SlotIdx)
    requires  Held(CAPS), Held(MEM), c.slots[s].used, ist_blatt(c, s)
    -- «B31» Die zweite Zeile ist NICHT ABLEITBAR, und zwar keine Fassung von ihr. `oldexpr`
    -- haengt unter `atompred` (:235-236), nicht unter `primary` (:200): `old(x)` kann als
    -- Praedikat FUER SICH stehen, aber nirgends in einem Ausdruck vorkommen — also auch
    -- nicht links oder rechts von `==`. Damit ist keine Differenzaussage schreibbar, und
    -- SYNTAX.md:292 gibt selbst eine an. Das trifft jede Nachbedingung, die „nachher gegen
    -- vorher" sagt — die haeufigste Form, die es gibt.
    ensures   !c.slots[s].used,
              o.slots[old(c.slots[s].object)].refcount + 1
                  == old(o.slots[c.slots[s].object].refcount)
    maintains cdt_wohlgeformt
    effects   { writes c.slots, writes o.slots, writes rf, allocs a, locks CAPS }
    costs     <= 200 ops
{
    let obj = c.slots[s].object;
    unlink(c, s);
    release_slot(c, s);

    -- «B29» -- UND SO SIEHT DIE AUFLOESUNG AUS (nachgezogen 2026-08-15).
    --
    -- Die Vorlage schrieb `refcount -= 1;` und prueefte DANACH auf Null. M1 verlangt den
    -- Nachweis VOR der Rechnung, und die Zaehlerregel (SPRACHE.md §1) sagt warum: ein
    -- Bereich am Typ sagt nichts darueber, ob die RECHNUNG darin bleibt.
    --
    -- Das Argument der Vorlage war: `refcount > 0` faellt aus der Buchfuehrungs-Invariante,
    -- und die ist nach «B13» nicht aufschreibbar. **Beides stimmt und beides hilft hier
    -- nicht** -- denn `narrow … else` verlangt keine Invariante, sondern eine PRUEFUNG. Der
    -- `else`-Zweig ist der Ort, an dem die Verletzung sichtbar wird, statt still zu wrappen.
    --
    -- Genau das ist der Unterschied zwischen EINEM Netz und ZWEIEN: die Invariante bleibt
    -- der Grund, warum der Zweig nie genommen wird; der Typ bleibt der Grund, warum er
    -- existieren muss.
    narrow o.slots[obj].refcount to 1 .. 80255 else {
        return Fehler::Buchfuehrung;
    }
    o.slots[obj].refcount -= 1;

    if o.slots[obj].refcount == 0 {
        -- «B28» Kein Platzhalterbinder: zehn Varianten ohne Nutzlastgebrauch brauchen zehn
        -- tote Namen. `_ =>` ist mit Absicht verboten, `_` als BINDER ist nicht vorgesehen.
        match o.slots[obj].kind {
            Memory(m)          => { free_region(a, m); }
            Dma(d)             => { push_dma(rf, d); }
            Reply(r)           => { push_reply(rf, r); }
            Endpoint(e1)       => { }
            Notification(n1)   => { }
            Tcb(t1)            => { }
            SchedContext(sc1)  => { }
            PdControl(pd1)     => { }
            Loader(l1)         => { }
            Mmio(mm1)          => { }
            Irq(i1)            => { }
            SyscallHandler(h1) => { }
            FaultHandler(f1)   => { }
        }
        o.slots[obj].gen  += 1;
        o.slots[obj].used  = false;
    }
}

impl fn revoke(c  : ptr<normal, rw> CapSpace,
               o  : ptr<normal, rw> CapObjects,
               a  : ptr<normal, rw+own> PhysAllocator,
               rf : ptr<normal, rw+own> Finalized,
               s  : SlotIdx)
    requires  Held(CAPS), Held(MEM), cdt_wohlgeformt(c)
    maintains cdt_wohlgeformt
    effects   { consumes c.slots, writes o.slots, writes rf, allocs a, locks CAPS }
    -- **«B34» -- DER GROESSTE EINZELBEFUND DIESES FRAGMENTS, und er kam vom Kostenpass.**
    --
    -- Die Vorlage sagte `<= 200 ops` zu. Sobald `CapSpace` seine Slotzahl nennt (`count
    -- NSLOTS`, nachgetragen 2026-08-15) und die Domaenenschranke damit steht, rechnet der
    -- Pass nach: **16 452 480 ops.** Fuenf Groessenordnungen.
    --
    -- Die 200 waren kein Tippfehler, sondern der TYPISCHE Fall -- ein `revoke` mit wenigen
    -- Nachfahren. `costs` ist aber eine SCHRANKE, und die Schranke eines `revoke` ueber
    -- einer 80 256-Slot-Tabelle ist die Tabelle. **Genau diese Verwechslung -- typischer
    -- Fall statt oberer Schranke -- ist der Grund, warum die Zahl nachgerechnet und nicht
    -- geglaubt wird**, und sie ist hier zum zweiten Mal aufgeschlagen (zuerst bei A4:
    -- 4 096 zugesagt, 831 488 gerechnet).
    --
    -- **BERICHTIGT 2026-08-15.** Hier stand: „Caprock begrenzt `revoke` ueber die
    -- CDT-Tiefe, und diese Schranke ist in Gabbro nicht ausdrueckbar." **Das war aus dem
    -- Gedaechtnis geschrieben und ist falsch.** `cdt_step_limit()` liefert
    -- `self.slots.len()` (`caprock-cap/src/space.rs:932-933`) -- **dieselbe Schranke, die
    -- Gabbro rechnet.**
    --
    -- Und der Kernel nimmt sie ZWEIMAL, innen und aussen (`:635`, `:648`); seine eigene
    -- obere Schranke ist `slots.len()^2`, also rund 390-mal groesser als diese Zahl.
    -- **Gabbros Schranke ist die schaerfere.** Es fehlt kein Konstrukt -- die 200 waren
    -- schlicht der typische Fall statt der Schranke, und genau dagegen ist der Kostenpass
    -- gebaut (`memos/M-kostenmass.md`).
    costs     <= 16452480 ops
{
    -- «B10» `traverse` liefert KEINEN Wert (:337-341) und es gibt kein `break`. Der
    -- Hoechststand `peak_revoke_ops` — im Rust-Original der Beleg dafuer, dass die Schranke
    -- nie gegriffen hat — ist damit nicht erhebbar. Die SCHRANKE faellt durch `by consuming`
    -- weg, die MESSUNG der Schranke ebenfalls, und nur die erste war beabsichtigt.
    traverse victim over descendants of c.slots[s] by consuming
        touches consumes c.slots, writes o.slots, writes rf
    {
        delete_leaf(c, o, a, rf, victim);
    }
}

-- Nachgetragen 2026-08-15: drei Gerufene wurden benutzt und nie erklaert. Ohne `costs` am
-- Gerufenen kann der Kostenpass die Zusage des Rufers nicht nachrechnen -- und er SAGT das
-- (`K003`), statt stillschweigend zu schaetzen. Genau dafuer ist die Absage da.
extern fn free_region(a : ptr<normal, rw> Allok, m : MemObj) effects { writes a } costs <= 32 ops;
extern fn push_dma(rf : ptr<normal, rw> Finalized, d : DmaObj) effects { writes rf } costs <= 8 ops;
extern fn push_reply(rf : ptr<normal, rw> Finalized, r : ReplyObj) effects { writes rf } costs <= 8 ops;


}
```

**Urteil: passt mit Befund** — «B1», «B2», «B10», «B13», «B14», «B15», «B16», «B28», «B29», «B31».

Der Rumpf traegt: `unlink` steht Zeile fuer Zeile, `delete_leaf` verliert den Auffangzweig ueber
zehn `ObjectKind`-Varianten (in Caprock sind seit Anlage **fuenf** Varianten dazugekommen — jede
waere still in `_ => {}` gefallen), und `revoke` schrumpft von 26 Rumpfzeilen auf 4, weil
`by consuming` Terminierung und Blattheit traegt. **Was nicht traegt, ist die Buchfuehrung selbst:**
`refcount_matches` ist nach «B13» unformulierbar, und `refcount -= 1` haengt genau daran.

**Was der Beweisteil braucht — und das ist KEIN Befund.** Zu diesem Fragment liegt im Scratchpad
ein zweiter Teil (`delete_leaf.beweis`, 7,2 KB): was ein Mensch **zusaetzlich** hinschreiben
muesste, damit die Pflichten durchgehen. Er braucht `ghost let`, `assert … by { … }`, `lemma …
requires … ensures … { Induktion ueber die Slot-Tabelle }` — und **keins** davon gibt es. Das ist
kein Loch, sondern die gezogene Linie: `SYNTAX.md`:567 fuehrt *„handgeschriebene Lemmata"*
ausdruecklich unter dem, was es nicht gibt, und :253-259 sagt den Preis dazu — es gibt keinen
Notausgang. **Der Beweisteil ist damit die Messung dieses Preises an einem echten Fall:** die
Erhaltung von `kind_zeigt_zurueck` durch `unlink` zerfaellt in vier Faelle, und Gabbro hat keine
Form, in der man sie fuehrt. Entweder faellt die Eigenschaft aus der Konstruktion, oder sie faellt
aus der Sprache heraus.

---

# F2 — VT-d: die Remapping-Einheit als `device`

**Herkunft:** `crates/caprock-hal/src/x86_64/vtd.rs:26-32` (Registerlagen), `:42-52`
(`GCMD_STATE_MASK` — Falle 4 woertlich), `:442` (`frr_off`), `:451` (`read_frr`), `:236-247`
(die Zustandsbits beim Kommandoschreiben).
**Vorlage im Scratchpad:** `vtd.gabbro` (155 Z.).

**Nachgezogen — und hier hat die neue Grammatik am meisten geholfen:** die Vorlage fuehrte
**sieben** Luecken, **vier** davon sind geschlossen. Mehrbitfelder (`ND`, `SAGAW`, `MGAW`, `FRO`,
`NFR`, `MAMV`, `IRO`, `TTM`, `RTA`, die CCMD-Felder) tragen jetzt `@[hi:lo]` (`bitpos`,
SYNTAX.md:146). Die Fault-Recording-Register und die IOTLB-Register liegen an **laufzeitberechneter**
Basis und sind als `bank … at CAP.FRO * 16 …` schreibbar (:429). Und die teuerste Luecke — *„es gibt
keine Form fuer: der Zustand dieses Registers wird aus jenem gelesen"* — ist `mirrors GCMD from
GSTS;` (:428). Mehrzeilige Zeichenketten in `assume` sind einzeilig gemacht (`char` schliesst
`newline` aus, :95).

**«B5»** Dabei faellt auf: der erklaerende Absatz zu Falle 4 (`SYNTAX.md`:453-458) spricht
weiterhin von *„keeping"* — einem Wort, das die Grammatik nicht mehr kennt. Die Datei fuehrt
ausdruecklich die Schreibregel, dass ein abgeschaffter Name kursiv in Anfuehrungszeichen steht und
**keine Syntax mehr ist** (:49-50); hier steht er in Backticks, also als heutige Syntax. Der
Waechter kann es nicht sehen: er prueft die Wortschatztabelle gegen die **EBNF**, nicht gegen die
Prosa.

```gabbro
device Vtd(base : Pa) at mmio {
    -- Falle 4, x86-Fassung: GCMD ist KEIN Read-Modify-Write. Genau eine Zeile, einmal je
    -- Geraet. Sie ersetzt `GCMD_STATE_MASK` samt der Kommentarwand in vtd.rs:42-52.
    mirrors GCMD from GSTS;

    reg VER  : u32 @0x000 class r  fields { MIN @[3:0], MAX @[7:4], }
    reg CAP  : u64 @0x008 class r
        fields { ND @[2:0], AFL @3, RWBF @4, PLMR @5, PHMR @6, CM @7, SAGAW @[12:8],
                 MGAW @[21:16], ZLR @22, FRO @[33:24], SLLPS @[37:34], PSI @39,
                 NFR @[47:40], MAMV @[53:48], DWD @54, DRD @55, FL1GP @56, PI @59,
                 FL5LP @60, ESIRTPS @62, ESRTPS @63, }
    reg ECAP : u64 @0x010 class r
        fields { C @0, QI @1, DT @2, IR @3, EIM @4, PT @6, SC @7, IRO @[17:8], SMTS @43, }
    reg GCMD : u32 @0x018 class w
        fields { CFI @23, SIRTP @24, IRE @25, QIE @26, WBF @27, EAFL @28, SFL @29,
                 SRTP @30, TE @31, }
    reg GSTS : u32 @0x01c class r
        fields { CFIS @23, IRTPS @24, IRES @25, QIES @26, WBFS @27, AFLS @28, FLS @29,
                 RTPS @30, TES @31, }
    reg RTADDR : u64 @0x020 class rw fields { TTM @[11:10], RTA @[63:12], }
    reg CCMD   : u64 @0x028 class rw
        fields { DID @[15:0], SID @[31:16], FM @[33:32], CAIG @[60:59], CIRG @[62:61],
                 ICC @63, }

    -- «B23» FSTS ist GEMISCHT: 7:0 sind RW1C, 15:8 (FRI, der Index des ersten besetzten
    -- Fault-Registers) sind r. `regdecl` (:430) traegt EINE Klassenangabe je Register.
    -- `class w1c` macht das Lesen von FRI untypisierbar — und FRI ist die Groesse, mit der
    -- der Treiber die Aufzeichnung ueberhaupt findet (vtd.rs:503).
    reg FSTS : u32 @0x034 class w1c
        fields { PFO @0, PPF @1, AFO @2, APF @3, IQE @4, ICE @5, ITE @6, PRO @7, FRI @[15:8], }

    reg IQH  : u64 @0x080 class r
    reg IQT  : u64 @0x088 class rw
    reg IQA  : u64 @0x090 class rw  fields { DW @11, }
    reg ICS  : u32 @0x09c class w1c fields { IWC @0, }
    reg IRTA : u64 @0x0b8 class rw  fields { EIME @11, }

    -- Geschlossen: Registerlage aus einem GELESENEN Feld. Der Index ist ueber `count`
    -- M1-beschraenkt; `frr_off` (vtd.rs:442) rechnet dieselbe Adresse von Hand aus.
    bank FRR at CAP.FRO * 16 stride 16 count 256 {
        reg FR_LO : u64 @0x0 class r
        -- «B24» Das F-Bit ist Bit 63 des OBEREN Wortes, `grund` liegt in 39:32 desselben.
        -- `bitpos` (:146) sagt nichts darueber, worauf sich eine Bitlage jenseits von 64
        -- bezieht und wie sie mit `endian` zusammenwirkt. Hier bezogen auf FR_HI.
        reg FR_HI : u64 @0x8 class w1c
            fields { SID @[15:0], TYPE @[29:28], GRUND @[39:32], AT @[61:60], F @63, }
    }
    bank IOTLB at ECAP.IRO * 16 stride 16 count 1 {
        reg IVA : u64 @0x0 class w
        reg CMD : u64 @0x8 class rw
            fields { DID @[47:32], DR @49, DW @50, IAIG @[58:57], IIRG @[60:59], IVT @63, }
    }

    -- «B26» Der Vorzustand steht an einem NICHT LESBAREN Ort. `mirrors` sagt, WOHER die
    -- mitgefuehrten Bits kommen; ob es damit auch den Vorzustand einer `transition` an
    -- `GCMD.TE` aus `GSTS.TES` bezieht, sagt SYNTAX.md (:428, :434) nicht. Die Vorlage hat
    -- diesen Widerspruch als unaufloesbar gefuehrt; er ist jetzt halb aufgeloest.
    transition setze_rtp { GCMD.SRTP: 0 -> 1 }
        requires GSTS.TES == 0 || GSTS.RTPS == 1
        effects  { writes GCMD }
    transition scharf_te { GCMD.TE: 0 -> 1 }
        requires GSTS.RTPS == 1
        effects  { writes GCMD }
    transition setze_irtp { GCMD.SIRTP: 0 -> 1 }
        requires GSTS.QIES == 1
        effects  { writes GCMD }
    transition scharf_ire { GCMD.IRE: 0 -> 1 }
        requires GSTS.IRTPS == 1 && GSTS.CFIS == 0
        effects  { writes GCMD }
    transition scharf_qie { GCMD.QIE: 0 -> 1 }
        requires GSTS.QIES == 0
        effects  { writes GCMD }
}

reason VtdFehler {
    KeineEinheit    = 1 "die ACPI-DMAR nennt keine Remapping-Einheit"
    Stumm           = 2 "deklariert, antwortet aber nicht (CAP == 0 oder alle Bits gesetzt)"
    Abgeschnitten   = 3 "die DMAR nennt mehr Einheiten als MAX_UNITS"
    KeineAgaw       = 4 "die Einheit bietet keine unterstuetzte Adressbreite"
    MgawZuKlein     = 5 "CAP.MGAW deckt die gewaehlte AGAW nicht"
    QiFehlt         = 6 "ECAP.QI aus, der Interrupt-Entry-Cache ist nicht invalidierbar"
    KeinSpeicher    = 7 "der Allokator lieferte kein Frame"
    NichtQuittiert  = 8 "die Einheit bestaetigte das Statusbit nicht"
    AufzeichnungVoll= 9 "FSTS.PFO, weitere Faults werden verworfen"
    exhaustive
}

-- «B25» `grund` soll genau die zwoelf Werte von FaultGrund tragen. `intty` traegt ein
-- INTERVALL (:139), keine Wertemenge. Hier geht es nur, weil 0x01..0x0c zufaellig
-- zusammenhaengend ist; bei einem geloecherten Code waere das Feld nicht bindbar.
-- «B24» Zweitens: der Satz besteht aus zwei 64-Bit-Woertern. Die Bitlagen unten sind auf
-- das jeweilige Wort bezogen, weil `format` (:393) keine Wortbreite kennt.
format FaultRecordLo @version 1 endian little {
    input_addr : u64 @[63:12] where (input_addr & 0xfff) == 0,
}

format FaultRecordHi @version 1 endian little {
    sid    : u16 @[15:0],
    typ    : u8  @[13:12],
    grund  : u8 in 0x01 .. 0x0c @[39:32],
    at     : u8  @[61:60],
    f_bit  : u8 in 1 .. 1 @63,
}
-- «B22-nah, eigener Fall» `where f_bit == 1` WEIST ein leeres Register AB, statt „leer" zu
-- MELDEN. Das ist der Unterschied zwischen Absage und Abwesenheit, und `format` kennt nur
-- die Absage. Im Rust-Original ist genau das der Unterschied zwischen „kein Fault" und
-- „Aufzeichnung nicht lesbar" (vtd.rs:451).

format Slpte @version 1 endian little {
    R    : u8  @0,
    W    : u8  @1,
    SNP  : u8  @11,
    ADDR : u64 @[63:12],
}

format ContextEntry @version 1 endian little {
    P        : u8  @0,
    FPD      : u8  @1,
    SLPTPTR  : u64 @[63:12],
    AW       : u8  @[66:64],
    DID      : u16 @[87:72],
}

assume vtd_te_wirkt
    "GCMD.TE schaltet die Uebersetzung scharf; DMA ohne Kontexteintrag faultet."
    falsifier probe_vtd_default_block;

assume gcmd_kein_rmw
    "GCMD wird als Ganzes geschrieben; ein nicht mitgeschriebenes Zustandsbit wird geloescht."
    unfalsifiable "eine Sonde muesste TE kurzzeitig loeschen, also genau das Fenster oeffnen, gegen das der Mechanismus gebaut ist";

assume fsts_pfo_verwirft
    "nach FSTS.PFO werden weitere Faults verworfen, bis F-Bit und PFO geloescht sind."
    falsifier probe_fault_overflow;
```

**Urteil: passt mit Befund** — «B23», «B24», «B25», «B26».

**Das ist das beste Ergebnis der sechs.** Von sieben Luecken der Vorlage sind vier zu, und die
teuerste davon war die x86-Fassung von Falle 4: `mirrors GCMD from GSTS;` ist **eine Zeile** gegen
eine Konstante plus elf Zeilen Kommentar plus zwei Fundstellen von Hand
(`vtd.rs:52`, `:236`, `:247`). Was bleibt, ist der Registerklassen-Befund («B23») — und der ist
nicht kosmetisch: er macht das Feld unlesbar, mit dem der Treiber die Fault-Aufzeichnung findet.

---

# F3 — IPC: der Fastpath `Endpoint::call`

**Herkunft:** `crates/caprock-ipc/src/lib.rs:611` (`call`), `:335` (`caller`); D11 sitzt im
Ueberlaufzweig der Senderschlange.
**Vorlage im Scratchpad:** `syntax-entwurf.md:1348-1456`.

**Nachgezogen:** `state X over Y` → `state X` (:414 kennt kein `over`) · `Some(x) -> { }` →
`Some(x) => { }` (:320) · `costs … cycles` → `ops` · `over e.receivers` → `over queue e.receivers`
(:242) · `Queue(ThreadId, QUEUE_CAP)` → monomorpher Verbund `TidQueue`.

```gabbro
module caprock::ipc {

const QUEUE_CAP : u32 = 32;
const NCORES    : u32 = 64;   -- nachgetragen 2026-08-15
const MSG_WORDS : u32 = 6;

reason IpcResult {
    Ok           = 0 "Rendezvous vollzogen"
    ErrBadCap    = 2 "Endpoint nicht belegt"
    ErrQuiescing = 8 "Endpoint stillgelegt, keine neue Transaktion"
    ErrEpFull    = 9 "Warteschlange voll, D11: benannt statt still"
    exhaustive
}

-- «B15» Monomorph ausgeschrieben. `Queue(T, const N)` ist nicht schreibbar: `typeexpr`
-- (:137) hat keine Anwendungsform, und `params` (:150) nimmt Werte, keine Typen.
type TidQueue = {
    buf   : [u32; 32],
    head  : u32 in 0 ..< 32,
    tail  : u32 in 0 ..< 32,
    count : u32 in 0 .. 32,
};

table Endpoint count NCORES {
    slot {
        used        : bool,
        quiescing   : bool,
        senders     : TidQueue,
        receivers   : TidQueue,
        caller      : option index into Threads,
        reply_owner : option index into Threads,
    }

    invariant antwortpflicht_paarig cost O(1) runs online :
        forall e in slots of Self :
            (Self.slots[e].caller == None) == (Self.slots[e].reply_owner == None);
}

-- «B17» HIER BRICHT DAS FRAGMENT. `transition` (:434) schreibt GENAU EIN `place`:
--     transition = "transition" ident "{" place ":" expr "->" expr "}" …
-- Die ganze Aussage des Fragments ist aber, dass `caller` und `reply_owner` NIE HALB
-- gesetzt werden — zwei Orte in EINEM Zug. In Caprock steht das als Kommentar
-- ("stets gemeinsam gesetzt/geloescht"); Gabbro sollte es zur Ableitung machen und kann es
-- nicht. Zweitens nennt `state` (:414) den Typ nicht, ueber dem es steht.
-- Drittens bindet `Some(cl)` im Zielausdruck einen frischen Namen — dafuer gibt es keine
-- Produktion. Die drei Zeilen unten sind AUSKOMMENTIERT, weil sie nicht schreibbar sind:
--     state Rendezvous over Endpoint {
--         transition open  { caller : None -> Some(cl), reply_owner : None -> Some(sv) }
--         transition close { caller : Some(c) -> None,  reply_owner : Some(s) -> None }
--     }

-- «B12» `forall i in 0 ..< MSG_WORDS` ist nicht schreibbar: die sieben Domaenen (:238-244)
-- enthalten keinen Zahlenbereich. Ersatz ueber `elems of` — und damit steht die zweite
-- Frage im Raum: bindet `elems of` ein ELEMENT und `slots of` einen INDEX? SYNTAX.md
-- benutzt beide Lesarten und legt keine fest.
spec fn msg_kopiert(dst : ptr<normal, r> Frame, src : ptr<normal, r> Frame) -> bool
    effects { pure }
    = forall i in elems of dst.msg : dst.msg[i] == old(src.msg[i]);

-- «B9» Der Ersatz fuer `&mut dyn SchedOps`: `fnptr` (:148) traegt KEINEN Vertrag —
-- kein `requires`, kein `ensures`, kein `effects`. Genau dafuer war der Verbund gedacht
-- ("der Vertrag des Rueckrufs muss am Zeigertyp stehen"). Er traegt nur noch die Signatur.
-- «B8» Und gerufen werden kann durch ihn ueberhaupt nicht: `call = path "(" … ")"` (:202);
-- `ops.current_id(core)` ist kein `call`, weil `ops.current_id` ein `place` ist.
type SchedOps = {
    current_id    : fn(u32) -> u32,
    frame_of      : fn(u32) -> u64,
    block_current : fn(u32, u64) -> u64,
    switch_to     : fn(u32, u64, u32) -> u64,
    unblock       : fn(u32) -> u32,
};

impl fn call(e    : ptr<normal, rw> Endpoint,
             dienste : ptr<normal, r> SchedOps,
             core : index into Endpoint,
             f    : ptr<normal, rw+own> Frame) -> ptr<normal, rw+own> Frame
    -- «B6» Die Nachbedingungen des Originals sprechen ueber `result`. `fndecl` (:266-274)
    -- bindet fuer den Rueckgabewert KEINEN Namen; `old(place)` gibt es, ein `result` nicht.
    requires  Held(EPS), e.slots[core].used
    maintains antwortpflicht_paarig
    -- `reads dienste` steht hier, weil `current_id`/`frame_of` es nennen: seit 2026-08-15
    -- schliesst eine Wirkungsliste die der Gerufenen ein (`E008`). **Die Zeile war vorher
    -- unvollstaendig, und kein Werkzeug konnte es sagen** -- genau der Posten, der `effects`
    -- erst kompositional macht.
    effects   { writes e.slots, locks SCHEDS, writes frames, consumes e.slots,
                reads dienste }
    costs     <= 2000 ops
{
    if e.slots[core].quiescing {
        set_reg(f, SYSNO_RESULT, IpcResult::ErrQuiescing);
        return f;
    }
    let caller = current_id(dienste, core);

    -- «B10» Der Fastpath sucht den ERSTEN lebenden Empfaenger und hoert dann auf. `traverse`
    -- liefert keinen Wert und kennt kein `break` — mit `by consuming` wird deshalb die
    -- GANZE Warteschlange geleert, auch die Empfaenger hinter dem gefundenen. Das ist keine
    -- Wortreichheit, sondern ein anderes Programm: aus einem Rendezvous wird ein Aderlass.
    let mut picked : u32 = KEIN_SERVER;
    traverse cand over queue e.slots[core].receivers by consuming
        touches consumes e.slots, reads sched
    {
        if picked == KEIN_SERVER && frame_of(dienste, cand) != KEIN_FRAME {
            picked = cand;
        }
    }

    if picked == KEIN_SERVER {
        let q = enqueue(e.slots[core].senders, caller) else (fehler) {
            -- D11 woertlich: der Ueberlaeufer wird NICHT blockiert, sondern benannt
            -- abgewiesen. Das traegt die Grammatik, und es ist der beste Zug in F3.
            set_reg(f, SYSNO_RESULT, IpcResult::ErrEpFull);
            return f;
        }
        return block_current(dienste, core, f);
    }

    transfer(f, frame_of(dienste, picked));
    set_reg(frame_of(dienste, picked), SYSNO_RESULT, IpcResult::Ok);
    set_reg(frame_of(dienste, picked), EP_BADGE, 0);
    -- «B17» hier stuende `open(e, caller, picked);` — der Uebergang, der beide Orte in
    -- EINEM Zug schreibt. Ohne ihn zwei Zuweisungen, und die Invariante gilt dazwischen nicht.
    e.slots[core].caller      = Some(caller);
    e.slots[core].reply_owner = Some(picked);
    if owner_core(picked) == core {
        return switch_to(dienste, core, f, picked);
    }
    unblock(dienste, picked);
    return block_current(dienste, core, f);
}


-- Nachgetragen 2026-08-15: `set_reg` wurde zweimal gerufen und nie erklaert.
extern fn set_reg(f : ptr<normal, rw> Frame, r : RegNr, w : u64) effects { writes f } costs <= 2 ops;
extern fn enqueue(q : ptr<normal, rw> TidQueue, t : u32) effects { writes q } costs <= 4 ops;
extern fn block_current(d : ptr<normal, r> SchedOps, core : index into Endpoint,
                        f : ptr<normal, rw> Frame) -> u32
    effects { reads d, writes f } costs <= 8 ops;
extern fn switch_to(d : ptr<normal, r> SchedOps, core : index into Endpoint,
                    f : ptr<normal, rw> Frame, t : u32) -> u32
    effects { reads d, writes f } costs <= 12 ops;
extern fn unblock(d : ptr<normal, r> SchedOps, t : u32) effects { reads d } costs <= 4 ops;
extern fn owner_core(d : ptr<normal, r> SchedOps, t : u32) -> u32
    effects { reads d } costs <= 2 ops;
extern fn transfer(f : ptr<normal, rw> Frame, g : u32) effects { writes f } costs <= 6 ops;

extern fn current_id(d : ptr<normal, r> SchedOps, core : index into Endpoint) -> u32
    effects { reads d } costs <= 2 ops;
extern fn frame_of(d : ptr<normal, r> SchedOps, t : u32) -> u32
    effects { reads d } costs <= 2 ops;
}
```

**Urteil: passt NICHT** — «B17» ist toedlich, dazu «B6», «B8», «B9», «B10», «B12», «B15».

Die Begruendung ist keine Geschmacksfrage: das Fragment wurde geschrieben, um zu zeigen, dass
Caprocks Kommentar *„`caller` und `reply_owner` werden stets gemeinsam gesetzt und geloescht"* in
Gabbro eine **Ableitung statt einer Zusage** wird. Mit einem `transition`, das einen Ort schreibt,
bleibt es eine Zusage — und zwischen den beiden Zuweisungen steht ein Zustand, in dem
`antwortpflicht_paarig` verletzt ist und den kein Konstrukt beschreibt. Dazu kommt «B10»: der
Fastpath **veraendert sein Verhalten**, wenn man ihn auf `traverse` ohne Ausstieg umschreibt.
**Zwei tragende Aussagen, beide weg.** Was traegt, ist D11 — und das ist bemerkenswert genug, um
es zu nennen: `let … else` erzwingt den Misserfolgszweig, ein stiller 33. Sender ist nicht
schreibbar.

**Drei Zusagen der Vorlage habe ich NICHT uebernommen, und der Grund ist keine Grammatikfrage.**
`syntax-pruefung-teil2.md` (G1–G3) hat sie gegen `crates/caprock-ipc/src/lib.rs:620-656` gehalten:

* `ensures e.caller is Some(cl) => cl == current_id(ops, core)` ist **falsch**, nicht bloss
  unbewiesen. Ruft ein zweiter Thread B, waehrend das Rendezvous mit A offen ist, landet B im
  `None`-Zweig (`:652`), `caller` bleibt `Some(A)` — die Zusage behauptet `A == B`. Das ist genau
  der Zustand, fuer den `senders` ueberhaupt existiert.
* `msg_copied` ist deklariert, in der eigenen Kennzahl **mitgezaehlt** und haengt an **keinem**
  `ensures`. Die einzige funktionale Eigenschaft eines Fastpaths — *die Nachricht ist angekommen* —
  gattert nichts, waehrend `transfer(f, …)` ohne jede Nachbedingung danebensteht. Woertlich die
  bezahlte Falle *„ein Negativtest kann eine Eigenschaft absichern, die niemand benutzt"*, eine
  Ebene hoeher.
* Das `effects` nennt `locks SCHEDS[core]`, der Cross-Core-Zweig nimmt aber zusaetzlich die Sperre
  eines **fremden** Kerns (`unblock`). Oben steht deshalb `locks SCHEDS` ohne Index — das ist
  ausgewichen, nicht geloest.

**Die Lehre daraus gehoert nicht zur Grammatik, sondern zur Buchfuehrung ueber sie:** eine
Kennzahl, die aus **ungepruften Zusagen** gebildet wird, belohnt die falsche Zusage, weil sie kurz
ist.

---

# F4 — Der Treiber: virtio-Transport, Ring, Puffereigentum

**Herkunft:** `crates/caprock-virtio/src/lib.rs:88-90` (Registerlagen), `:334` (`publish`),
`:363` (`poll_used`), `:494-499` (`QUEUE_SIZE` als fremde Zahl), `:533` (das von Hand
zusammengesetzte Statuswort), `crates/caprock-virtio/src/owned.rs` (Puffereigentum).
**Vorlage im Scratchpad:** `grammatik-v3.md:112-274`.

**Nachgezogen:** `where Self <= QMAX else QueueTooBig` → `requires Self <= QMAX` (`regdecl`,
:433) · `fields { … }` mit Schlusskomma (:432) · `retry` in der Reihenfolge der Produktion
(:343-348) · `touches { … }` → `touches` ohne Klammern (:340, **«B30»**).

```gabbro
device VirtioPci(base : Pa) at mmio {
    reg DEVICE_FEATURE_SEL : u32 @0x00 class w
    reg DEVICE_FEATURE     : u32 @0x04 class r
    reg DRIVER_FEATURE_SEL : u32 @0x08 class w
    reg DRIVER_FEATURE     : u32 @0x0c class w
    reg DEVICE_STATUS      : u8  @0x14 class rw
        fields { ACK @0, DRIVER @1, DRIVER_OK @2, FEATURES_OK @3, }
    reg QUEUE_SELECT       : u16 @0x16 class w
    -- «B26» `QUEUE_SIZE` ist eine FREMDE Zahl (lib.rs:494). `regdecl` traegt ein
    -- `requires`, aber keinen benannten Ausgang: aus „zu gross" wird kein `reason`-Wert.
    -- Die Vorlage schrieb `else QueueTooBig`; das gibt es nicht.
    reg QUEUE_SIZE         : u16 @0x18 class rw requires QUEUE_SIZE <= QMAX
    reg QUEUE_ENABLE       : u16 @0x1c class w
    reg QUEUE_NOTIFY_OFF   : u16 @0x1e class r
    reg QUEUE_DESC         : u64 @0x20 class w
    reg QUEUE_DRIVER       : u64 @0x28 class w
    reg QUEUE_DEVICE       : u64 @0x30 class w

    -- Das traegt, und es ist der Gewinn dieses Fragments: `transition` nennt das GANZE
    -- geschriebene Wort. lib.rs:533 setzt es an vier Stellen von Hand zusammen.
    transition ack    { DEVICE_STATUS: 0 -> ACK } effects { writes DEVICE_STATUS }
    transition drv    { DEVICE_STATUS: ACK -> ACK | DRIVER } effects { writes DEVICE_STATUS }
    transition featok { DEVICE_STATUS: ACK | DRIVER -> ACK | DRIVER | FEATURES_OK }
        effects { writes DEVICE_STATUS }
    transition drvok  { DEVICE_STATUS: ACK | DRIVER | FEATURES_OK
                                    -> ACK | DRIVER | FEATURES_OK | DRIVER_OK }
        effects { writes DEVICE_STATUS }
    -- «B26» `transition reset { DEVICE_STATUS: any -> 0 }` ist nicht schreibbar: es gibt
    -- keinen Platzhalter fuer den Vorzustand. Ein Reset gilt aus JEDEM Zustand — genau die
    -- Aussage, die eine Uebergangstabelle braucht, damit sie vollstaendig ist.
}

-- «B18» HIER BRICHT DIE HAELFTE VON F4. Die Vorlage schrieb den Ring als `device` mit
-- Phasen und einer Registerklasse JE PHASE:
--     phases { Setup, Live }
--     reg USED_IDX : u16 wrapping @0x202 class rw in Setup, r in Live
-- `device` (:426-435) kennt keine Phasen, und `regdecl` (:430) traegt eine Klasse.
-- Damit ist „`used` gehoert dem Geraet" wieder ein Kommentar. Dieselbe Stelle traegt eine
-- BEZAHLTE Falle: bei einer wiederverwendeten Region steht im `used`-Ring der Endstand der
-- vorigen Treiberfassung, und die Vorlage machte daraus die `requires`-Klausel von `enable`.
-- «B20» Dazu: `wrapping` gehoert an `slottype` (:388), nicht an `intty` (:139). Der
-- avail-Index ist ein REGISTER und laeuft laut virtio-Spezifikation bei 65536 um; als
-- `u16 in 0 ..< n` waere er falsch, als `u16 wrapping` nicht schreibbar.
-- «B19» Und die Barrieren: `AVAIL_IDX … publishes { DESC, AVAIL_RING } release` ist die
-- Form, aus der der Uebersetzer die fuenf `fence()`-Aufrufe des echten Treibers ableiten
-- sollte. `publishes` sitzt an `atomicdecl` (:468) — das nach «B2» nicht einmal erreichbar
-- ist — und nicht an einem Geraeteregister. SYNTAX.md fuehrt genau das als offenen Punkt
-- (:598): die sicherheitskritischste Veroeffentlichung im Baum ist gar kein Atomic.

device Virtq(base : Iova, n : u16 in 1 .. QMAX) at dma {
    bank DESC at 0x000 stride 16 count 256 {
        reg addr  : u64 @0x0 class w
        reg len   : u32 @0x8 class w
        reg flags : u16 @0xc class w fields { NEXT @0, WRITE @1, }
        reg naechst : u16 @0xe class w
    }
    reg AVAIL_FLAGS : u16 @0x100 class rw
    reg AVAIL_IDX   : u16 wrapping @0x102 class rw
    bank AVAIL_RING at 0x104 stride 2 count 256 { reg e : u16 @0x0 class w }
    reg USED_FLAGS  : u16 @0x200 class rw
    reg USED_IDX    : u16 @0x202 class rw
    bank USED_RING at 0x204 stride 8 count 256 {
        reg id  : u32 @0x0 class rw
        reg len : u32 @0x4 class rw
    }
}

-- Der Ersatz fuer die Phasen ohne neuen Mechanismus: die Phase ist ein linearer
-- Geisterwert, woertlich `BootPhase` eine Ebene tiefer. Nach `queue_arm` gibt es keinen Weg
-- mehr, `USED_IDX` zu schreiben — nicht weil ein Waechter es verbietet, sondern weil die
-- Marke verbraucht ist.
-- «B3» `linear ghost type QueueSetup(Virtq);` schreibt eine TYPliste in die Klammern.
-- `typedecl` (:135-136) verlangt dort `params`, also `ident ":" typeexpr`. SYNTAX.md
-- macht denselben Fehler in seinen eigenen vier Beispielen (:162-167), `Held(Lock)`
-- eingeschlossen — und `Held` steht in jedem `requires` dieser Datei.
linear ghost type QueueSetup(Virtq);

fn queue_reset(q : ptr<dma, rw> Virtq) -> QueueSetup
    effects { writes q };

fn queue_arm(q : ptr<dma, w> Virtq, s : QueueSetup)
    effects { writes q, consumes s };

tagged type BufPhase = { Driver, Device };

reason UnprovenReason {
    StatusByteProbe = 1 "blk liest das Statusbyte auch nach dem Poll-Timeout: bleibt es 0xff, hat das Geraet nichts geschrieben"
    exhaustive
}

impl fn publish(q : ptr<dma, rw> Virtq, head : u16 in 0 ..< 256)
    effects { writes q }
    -- Nachgezogen 2026-08-15: die Vorlage sagte `<= 4 ops` zu, der Rumpf kostet 9. Die Zahl
    -- ist mit `gabbro kosten` abgelesen, nicht geschaetzt (WERKZEUGKASTEN.md W2).
    costs   <= 9 ops
{
    -- Der Nenner schliesst die Null aus, weil `n : u16 in 1 .. QMAX` es tut (:216).
    let platz = q.AVAIL_IDX % q.n;
    q.AVAIL_RING[platz].e = head;
    -- Nachgezogen 2026-08-15: der Ringzaehler LAEUFT UEBER, und zwar mit Absicht --
    -- virtio zaehlt modulo 2^16 und nimmt den Rest gegen `q.n`. Die Vorlage schrieb
    -- `+= 1` auf einem blanken `u16`; damit stand die Absicht nirgends, und die
    -- Zaehlerregel (SPRACHE.md §1) faellt zu Recht.
    --
    -- **«B32» -- UND HIER FAELLT EIN NEUER BEFUND.** Die Sprache laesst den Umlauf an der
    -- DEKLARATION aussprechen, nicht an der Rechnung: `slottype = intty "wrapping"`
    -- (SYNTAX.md:500). Das ist die staerkere Form -- der Umlauf gilt dann fuer jede Rechnung
    -- auf dem Feld, nicht nur fuer die eine, an die jemand gedacht hat.
    --
    -- **Aber `AVAIL_IDX` ist kein Slot, sondern ein REGISTER**, und `regdecl` (:545-548)
    -- kennt `wrapping` nicht. Ein Hardwarezaehler, der per Entwurf umlaeuft -- der
    -- haeufigste Fall ueberhaupt in einem Geraetetreiber -- kann seine Absicht nicht
    -- aussprechen. Bis das geschlossen ist, steht hier die Pruefung davor; sie ist an
    -- dieser Stelle NICHT die ehrliche Form, sondern der Ersatz dafuer.
    -- **«B32» ist geschlossen (2026-08-15), und der Ersatz faellt weg.** Bis dahin stand
    -- hier ein `narrow` mit einem `else`-Zweig, der die Absicht NICHT ausdrueckte, sondern
    -- umging. Jetzt sagt die Deklaration `reg AVAIL_IDX : u16 wrapping`, was virtio meint,
    -- und die Rechnung darf schlicht dastehen.
    --
    -- «B33» bleibt daneben offen: die V-Regeln verengen den Typ eines REGISTERORTES nach
    -- `if … == N { return; }` nicht -- nur `narrow` traegt die Tatsache. Ob das Absicht ist
    -- (ein Register kann sich zwischen Pruefung und Rechnung aendern!) oder eine Luecke,
    -- entscheidet der Ordner. **Wenn es Absicht ist, gehoert die Begruendung
    -- aufgeschrieben** -- sie waere ein starkes Argument.
    q.AVAIL_IDX += 1;
}

impl fn poll_used(q : ptr<dma, r> Virtq, von : u16) -> u32
    effects { reads q }
{
    -- Das traegt unveraendert, und die Reihenfolge stimmt mit der Produktion (:343-348):
    -- bounded, progress, on_exceeded, effects. Der Ueberlauf ist BENANNT.
    retry warten until q.USED_IDX != von
        bounded     MAX_POLL ops
        progress    device_completes_or_faults
        on_exceeded DeviceSilent
        effects     { reads q }
    { }
    let s = von % q.n;
    -- «B7» `return Completion { id: …, len: … };` ist nicht schreibbar: `primary` (:200)
    -- kennt keinen Verbund- und keinen Feldliteral. Eine Funktion kann einen `structty`
    -- also nicht HERSTELLEN. Deshalb hier ein Skalar statt des Verbunds.
    return q.USED_RING[s].id;
}
```

**Urteil: passt mit Befund** — «B3», «B7», «B18», «B19», «B20», «B26», «B30».

Der Transport traegt vollstaendig und nimmt Falle 4 in ihrer virtio-Fassung mit: das Statuswort
wird nicht mehr von Hand zusammengesetzt. `retry` traegt den Poll wortgleich. **Der Ring traegt
nicht:** Phasen, Registerklasse je Phase und `publishes` am Geraeteregister fehlen alle drei, und
sie tragen zusammen zwei bezahlte Fallen (wiederverwendete Virtqueue, Barriere aus dem Adressraum).
Der Ersatz ueber einen linearen Geisterwert traegt die erste — und braucht dafuer «B3».

---

# F5 — Userspace: die Dienstschleife von `virtio-blk`

**Herkunft:** `programs/hardware/virtio-blk/src/main.rs:255` (`run`), `:317` (die Schleife),
`:418` (`OP_STOP`), `:92` (die Op-Codes); `programs/libcaprock/src/lib.rs` (der Syscall-Einstieg).
**Vorlage im Scratchpad:** `grammatik-v3.md:317-408`.

**Nachgezogen:** `fn run … -> never` → `divergent fn` (`nevertype` ist laut :138 der Rueckgabetyp
von `prim`/`divergent`) · Match-Arme als Bloecke (:320) · `costs`-Einheit.

```gabbro
module programs::virtio_blk {

reason Status {
    Ok      = 0 "alles gut"
    Device  = 1 "das Geraet antwortete nicht oder meldete einen Fehler"
    BadOp   = 2 "unbekannte Operation"
    Range   = 3 "der Bereich liegt nicht auf der Platte: Fehler des Clients, nicht des Geraets"
    NoTable = 4 "keine lesbare Partitionstabelle"
    exhaustive
}

reason ServiceExit {
    EndpointGone = 1 "der Endpoint ist stillgelegt oder entzogen, Hot-Reload der alten Fassung"
    Stopped      = 2 "OP_STOP: der Client hat den Dienst beendet, die Antwort ging noch raus"
    exhaustive
}

tagged type Op = { Info, Read, Write, Flush, Scan, Stop };

-- «B27» Der Syscall-Einstieg: `arch ident` gibt es (:273), die REGISTERBELEGUNG nicht.
-- Die Vorlage schrieb dafuer einen `abi { in rax = nr, …, trap 0x80 }`-Block; `fndecl`
-- kennt ihn nicht. Damit hat der einzige Ort, an dem 168 gemessene `asm!`-Stellen
-- zusammenlaufen sollten, in der Grammatik keinen Traeger — die vertrauenswuerdige Flaeche
-- schrumpft nicht, sie wandert in eine `prim`-Deklaration ohne Inhalt.
prim fn invoke(nr : u64, cap : u64, m0 : u64, m1 : u64, m2 : u64, m3 : u64, tag : u64) -> u64
    effects { writes machine_regs }
    arch x86_64;

prim fn invoke(nr : u64, cap : u64, m0 : u64, m1 : u64, m2 : u64, m3 : u64, tag : u64) -> u64
    effects { writes machine_regs }
    arch aarch64;

divergent fn run(startwert : u64) -> never
    effects { diverges, writes DMA, writes SHARED, reads EP }
{
    let cfg    = map_window(CFG)    else (e1) { signal(NTFN, 0xD1A6_0001); exit(); }
    let bar    = map_window(BAR)    else (e2) { signal(NTFN, 0xD1A6_0002); exit(); }
    let dmafenster    = map_window(DMA)    else (e3) { signal(NTFN, 0xD1A6_0003); exit(); }
    let teilfenster = map_window(SHARED) else (e4) { signal(NTFN, 0xD1A6_0004); exit(); }

    let pool      = pool_new(dmafenster)    else (e5) { signal(NTFN, 0xD1A6_0000); exit(); }
    let transport = probe_ecam(cfg)  else (e6) { signal(NTFN, 0xD1A6_00FF); exit(); }

    signal(NTFN, 0);

    -- «B14» `let mut capacity : option Sectors = none;` ist nicht schreibbar: `option` steht
    -- nur in `slottype` (:387), nicht in `typeexpr` (:137). Der Fall „noch nie gelesen" wird
    -- damit wieder eine 0 — genau die Deutung, gegen die das Fragment geschrieben war.
    let mut capacity : u32 = 0;

    -- «B11» HIER BRICHT F5. `forever` (:350-354) hat KEINEN AUSGANG. Die Vorlage schrieb
    --     awaits recv(EP)   leaves ServiceExit   …   { … leave EndpointGone; }
    -- und begruendete es mit D0: der echte Code hat an dieser Stelle
    -- `if m.result != OK { break; }`, und dass dieser Austritt keinen Namen trug, hat zehn
    -- Tage gekostet. In der Grammatik von heute gibt es weder `leave` noch `break` noch
    -- `continue`; SYNTAX.md fuehrt das selbst als offenen Punkt (:603) und vermutet, es sei
    -- versehentlich. Es ist der Unterschied zwischen „D0 faellt durch Konstruktion" und
    -- „die Dienstschleife ist nicht schreibbar".
    forever dienst
        per_pass bounded MAX_POLL ops
        on_exceeded watchdog_schlug_an
        effects  { reads EP, writes SHARED, writes pool }
        progress    client_calls_or_endpoint_revoked
    {
        let m = recv(EP) else (e7) { exit(); }
        match decode_op(m.op) {
            Info => {
                let r = request_flush(transport, pool);
                capacity = r;
                -- «B7» `reply(EP, [Ok, r, MAX_SECTORS, SECTOR]);` ist nicht schreibbar:
                -- `primary` (:200) kennt kein Feldliteral. Vier Argumente statt eines Feldes.
                reply4(EP, Status::Ok, r, MAX_SECTORS, SECTOR);
            }
            Read  => { serve_rw(EP, transport, pool, teilfenster, m, capacity); }
            Write => { serve_rw(EP, transport, pool, teilfenster, m, capacity); }
            Flush => {
                let r2 = request_flush(transport, pool);
                reply4(EP, Status::Ok, 0, 0, bump_served(pool));
            }
            Scan  => { serve_scan(EP, transport, pool); }
            Stop  => {
                reply4(EP, Status::Ok, 0, 0, 0);
                -- «B11» hier stuende `leave Stopped;`. Ohne Ausgang bleibt nur `exit()` —
                -- also der Sprung aus der ganzen Funktion, und die Aufraeumzusage der
                -- Funktion wandert an zwei Stellen. Das ist woertlich die Klasse, die C8
                -- bezahlt hat: ein neuer Abweispfad erbt die Aufraeumpflicht des alten nicht.
                exit();
            }
        }
    }
}

-- Nachgetragen 2026-08-15: `exit` und `signal` wurden benutzt und nie erklaert.
-- Ohne `-> never` an `exit` kann kein Pass sehen, dass die Fehlerzweige nicht
-- durchfallen -- sechs `S002` kamen allein daher.
extern fn exit() -> never effects { diverges };
extern fn signal(n : u64, w : u64) effects { writes NTFN };
extern fn watchdog_schlug_an() -> never effects { diverges };

}
```

**Urteil: passt NICHT** — «B11» ist toedlich, dazu «B7», «B14», «B27».

Was traegt, traegt gut: `match` ist erschoepfend, also gibt es den `_ => reply(ST_BADOP)`-Zweig in
jedem Server nicht mehr, sondern **einmal** in `decode_op`; die vier `map_window`-Absagen sind
ueber `let … else` erzwungen statt gewuenscht. Was nicht traegt, ist die **Form** des Programms:
ein Dienst ist eine Schleife, die auf einen Endpoint wartet und ihn **benannt** verlassen koennen
muss. `forever` gibt es, einen Ausgang nicht — und `retry until pred` ist das falsche Konstrukt
(es wiederholt, **bis** `pred` gilt; hier soll **bei** `pred` beendet werden, und der Rumpf ist
kein Wiederholungsversuch).

---

# F6 — Pruefgeruest: die Stack-Wasserstandsmarke

**Herkunft:** `kernel/src/kstackmark.rs:145` (`unberuehrt`), `:192` (`messen`), `:199-203`
(`fetch_max`/`fetch_min`), `:372` (`marke`), `:432` (`MIND_MESSUNGEN`), `:445` (`urteil`),
`:281-283` (die Eichung).
**Vorlage im Scratchpad:** `grammatik-v3.md:456-588`.

**Nachgezogen — und hier hat die neue Grammatik zwei von drei Befunden der Vorlage geschlossen:**
`publishes nothing` gibt es jetzt (:469), `relaxed` auch (:470). Die Vorlage hatte beides als
Luecke gefuehrt: ein reiner Zaehler war *„entweder vertragsfrei oder ungrammatisch"*, und die
Ordnungsmenge hatte mit `Relaxed` das haeufigste Element ausgelassen (779 von 2257 gemessenen
Zugriffen) und mit `SeqCst` das nie benutzte aufgenommen.

```gabbro
module kernel::kstackmark {

reason Stackart {
    El0  = 0 "der 16-KiB-EL1-Stack eines EL0-Threads"
    Kern = 1 "der 64-KiB-Stack eines Kernel-Threads"
    exhaustive
}

const STACK_MAX : u64 = 65536;   -- nachgetragen 2026-08-15: benutzt, nie erklaert
type Bytes = u64 in 0 .. STACK_MAX;

const MIND_RESERVE_NENNER : u32 in 1 .. 64 = 8;
const MIND_MESSUNGEN      : u32 = 2;

-- «B2» Alle zehn Zeilen unten sind `atomicdecl` (:468) — von `program` aus NICHT
-- ERREICHBAR, weil `item` (:111-112) sie nicht auffuehrt. Sie stehen hier trotzdem, weil
-- sie sonst nirgends stehen koennten; ein Modul, das sie enthaelt, ist heute nicht
-- ableitbar. Betrifft baumweit 594 Atomic-Deklarationen.
-- «B21» `accumulates max` / `accumulates min` / `accumulates +` gibt es nicht. Genau sie
-- SIND die Wasserstandsmarke (`TIEFE_MAX.fetch_max`, kstackmark.rs:199-203); ohne sie ist
-- die Messgroesse dieses Fragments nicht schreibbar. Baumweit 213 Lese-Aendere-Schreib-
-- Zugriffe, davon 19 `fetch_max`/`fetch_min`. SYNTAX.md fuehrt den Punkt selbst (:600) und
-- nennt ihn den ersten Kandidaten fuer „zwei geforderte Eigenschaften widersprechen einander".
-- «B14» `frei_min : option Bytes` ist nicht schreibbar (`option` nur als `slottype`). Der
-- echte Code rechnet spaeter `groesse.saturating_sub(frei_min)` und macht damit aus
-- „nie gemessen" eine 0 — die Deutung, die eine Nullmessung unsichtbar macht.
atomic gefuellt     : u32 publishes nothing relaxed;
atomic gemessen     : u32 publishes nothing relaxed;
atomic gemessen_tod : u32 publishes nothing relaxed;
atomic tiefe_max    : u64 publishes nothing relaxed;
atomic tiefe_tod    : u64 publishes nothing relaxed;
atomic tiefe_lebend : u64 publishes nothing relaxed;
atomic frei_min     : u64 publishes nothing relaxed;
atomic erschoepft   : u32 publishes nothing relaxed;
atomic groesse      : u64 publishes nothing relaxed;
atomic tiefster     : u32 publishes nothing relaxed;

impl fn unberuehrt(s : ptr<normal, r+own> Stack) -> u64
    ensures  unberuehrt <= s.len
    effects  { reads s }
{
    let mut i : u64 in 0 .. STACK_MAX = 0;
    -- «B30» `touches` nimmt eine `efflist` OHNE Klammern (:340), waehrend `effects`
    -- ueberall sonst geklammert ist. Die Vorlage schrieb `touches { reads s }`.
    traverse w of s over elems of s.worte by decreasing (lenof(s.worte) - i)
        touches reads s
    {
        if w != MUSTER { return i * 8; }
        -- Nachgezogen 2026-08-15: die Schranke faellt zwar aus der Domaene (die
        -- Traversierung laeuft ueber `s.worte`), **aber M1 sieht das nicht** -- der
        -- Zaehler ist eine gewoehnliche lokale Variable. Die Pruefung VOR der Rechnung
        -- ist genau das, was die Zaehlerregel verlangt; der `else`-Zweig kann nicht
        -- genommen werden und muss trotzdem dastehen.
        narrow i to 0 .. 65535 else { return i * 8; }
        i += 1;
    }
    return i * 8;
}

-- «B7» Das Original gibt ein PAAR zurueck (`-> (benutzt, frei)`). `typeexpr` (:137) kennt
-- kein Tupel; der Ausweg waere ein `structty` — und den kann eine Funktion nach «B7» nicht
-- HERSTELLEN, weil es kein Verbundliteral gibt. Zwei Befunde, die einander blockieren:
-- deshalb hier zwei Funktionen und eine doppelte Traversierung.
-- «B6» `ensures benutzt + frei == s.len` benennt Rueckgabefelder. Es gibt keine Bindung
-- fuer den Rueckgabewert; oben behilft sich die Zeile mit dem Funktionsnamen, und das ist
-- geraten, nicht geschrieben.
impl fn messen_benutzt(s : ptr<normal, r+own> Stack, art : Stackart) -> u64
    requires  s.len >= 8
    effects   { reads s, writes tiefe_max, writes gemessen }
{
    let frei = unberuehrt(s);
    -- Das kommt durch, weil das `ensures` von `unberuehrt` `<= s.len` sagt: aus dem VERTRAG
    -- der gerufenen Funktion, nicht aus einer Flussregel. Kostet eine Zeile Nachbedingung,
    -- keinen Beweis.
    let benutzt = s.len - frei;
    -- «B21» hier stuenden `accumulate tiefe_max by benutzt;` und `accumulate frei_min by frei;`
    return benutzt;
}

-- «B22» `claim` nimmt eine Zeichenkette, und `char` (:95) schliesst `newline` aus. Alle drei
-- echten Behauptungen sind mehrzeilig; hier zusammengezogen. Eine Behauptung, die in eine
-- Zeile passen muss, wird kuerzer geschrieben, nicht genauer.
check kstack_eichung {
    claim    "Das Messgeraet meldet an einem Feld bekannter Tiefe genau diese Tiefe, an einem gefuellten unberuehrten Feld die volle Laenge, und an einem ungefuellten Feld null."
    measures eich.leer, eich.voll, eich.tiefe, eich.gelaufen
    gates    kstack
    can_fail {
        let f = eichfeld();
        if unberuehrt(f) != 0 { return false; }
        muster_schreiben(f);
        if unberuehrt(f) != f.len { return false; }
        beruehre(f, EICH_TIEFE_WORTE);
        if unberuehrt(f) != (lenof(f.worte) - EICH_TIEFE_WORTE) * 8 { return false; }
        return true;
    }
    floor    eich.gelaufen == 1
}

check kstack {
    claim    "Am Fuss jedes EL0-Kernel-Stacks bleibt mindestens ein Achtel der Stackgroesse unberuehrt, und tiefste Kette plus tiefster IRQ-Handler plus diese Reserve passen zusammen in die Groesse."
    measures gefuellt, gemessen_tod, tiefe_max, frei_min, erschoepft, groesse, tiefster,
             irq.tiefe_max, irq.n
    gates    all_done
    can_fail {
        -- «B14» `let g = groesse else (e) { return false; };` ist nicht schreibbar: die
        -- `let … else`-Form (:316) verlangt RECHTS einen `call`. Ein `option`-wertiges
        -- `place` laesst sich damit nicht auspacken — und ein Atomic ist ein `place`.
        let g = groesse_gemessen() else (e1) { return false; }
        let f = frei_min_gemessen() else (e2) { return false; }
        if f < g / MIND_RESERVE_NENNER { return false; }
        return (g - f) + irq.tiefe_max + g / MIND_RESERVE_NENNER <= g;
    }
    floor    gemessen_tod >= MIND_MESSUNGEN, groesse >= 1, irq.n >= 1
    counterprobe "Fuellung ausgehaengt" expects erschoepft_waechst
}

}
```

**Urteil: passt mit Befund** — «B2», «B6», «B7», «B14», «B21», «B22», «B30».

**`check` selbst traefe genau:** die `measures`-Liste **ist** die Berichtszeile (im echten Code
sind es drei Fassungen derselben Liste — eine Struktur `Marke` mit zehn Feldern, die Funktion, die
sie fuellt, und die Formatierungszeile); `floor` trifft genau die drei Sprechproben, die
`urteil()` von Hand fuehrt; und `gates kstack` an der Eichung ist die lineare Kette, die im echten
Code als freiwilliges erstes Konjunkt steht. **Was nicht traegt, ist die Messgroesse:** ohne
atomares Lese-Aendere-Schreibe («B21») gibt es keine Wasserstandsmarke, und ohne `option` als
Typ («B14») kehrt genau die Deutung zurueck, gegen die `floor` gebaut ist.

---

# Die Befunde

**31 Befunde. 7 sitzen in `SYNTAX.md` selbst** (B1–B6 und B31: Widersprueche zwischen EBNF, Prosa
und den eigenen Beispielen), **24 sind Luecken der Ausdrucksmittel**. Spalte „Zeile" ist die Zeile **in
dieser Datei**, an der der Befund verankert ist; Spalte „SYNTAX.md" nennt die betroffene
Produktion.

| # | Zeile | SYNTAX.md | Befund | trifft |
|---|---|---|---|---|
| **B1** | 171 | :266-274 gegen :287 | `spec fn … = pred;` benutzt die Datei selbst, `fndecl` laesst nur `block \| ";"`. Ueber einen `block` ist ein Quantor nicht erreichbar, weil `pred` nicht unter `expr` haengt | F1, F3, alle `spec fn` |
| **B2** | 124 | :111-112, :313-314 | `atomicdecl`, `lockdecl`, `lockstmt` sind definiert und von `program` aus **nicht erreichbar**. Maschinell nachgerechnet: 103 Regeln, 3 unerreichbar | F1, F3, F4, F6 — jede Sperre, jedes Atomic |
| **B3** | 744 | :135-136 gegen :162-167 | `linear ghost type Held(Lock);` schreibt eine Typliste, wo `params` `ident ":" typeexpr` verlangt. Vier eigene Beispiele, `Held` in jedem `requires` | alle sechs |
| **B4** | 22 | :295, :366 gegen :580 | `costs <= 200 cycles` im Beispiel gegen die Entscheidung „`costs` zaehlt Operationen". Die Einheit ist ein freier Bezeichner — kein Waechter kann es sehen | alle sechs |
| **B5** | 334 | :453-458 gegen :428 | Der Absatz zu Falle 4 erklaert *„keeping"*, ein Wort, das es nicht mehr gibt; die Produktion heisst `mirrors` | F2 |
| **B6** | 574 | :266-274 | Kein Name fuer den Rueckgabewert in `ensures`. `old(place)` gibt es, ein `result` nicht | F3, F4, F6 |
| **B7** | 785 | :200 | Kein Verbund- und kein Feldliteral in `expr`. Eine Funktion kann einen `structty` nicht herstellen; Tupelrueckgabe und `reply(EP, [ … ])` fallen mit | F4, F5, F6 |
| **B8** | 560 | :202 | Kein Aufruf durch ein `place`: `ops.current_id(core)` ist kein `call`, obwohl `fnptr` als Typ existiert | F3 |
| **B9** | 557 | :148 | `fnptr` traegt keinen Vertrag — der Ersatz fuer `&mut dyn SchedOps` verliert genau das, wofuer er da war | F3 |
| **B10** | 283 | :337-341 | `traverse` liefert keinen Wert, es gibt kein `break`. Die Suche nach dem ERSTEN Treffer wird zum Leeren der ganzen Menge; ein Operationszaehler ist nicht erhebbar | F1 (`peak_revoke_ops`), F3 (Fastpath) |
| **B11** | 862 | :350-354, :603 | `forever` hat keinen Ausgang; `leave`/`break`/`continue` gibt es nicht. Die D0-Lehre („ein namenloser Austritt aus der Serverschleife") ist nicht ausdrueckbar | **F5 toedlich** |
| **B12** | 549 | :238-244 | Keine Zahlenbereichs-Domaene (`forall i in 0 ..< MSG_WORDS`); und ob `slots of` einen Index oder einen Slot bindet, ist nicht festgelegt — beide Lesarten kommen in der Datei vor | F1, F3, F6 |
| **B13** | 165 | :230-247 | Keine Aggregation (`count`) und keine tabellenuebergreifende Domaene in `pred`. `refcount_matches` — die Buchfuehrung des Faehigkeitssystems — ist nicht formulierbar | F1 |
| **B14** | 162 | :137, :387, :316 | `option` gibt es nur als `slottype`, nicht als `typeexpr`; und `let … else` verlangt rechts einen `call`, packt ein `place` also nicht aus | F1, F5, F6 |
| **B15** | 111 | :137, :147, :150 | Keine Typanwendung: `Outcome(T,E)`, `Queue(T,N)` unschreibbar; `variants` nimmt je Variante genau einen `typeexpr`, Mehrfeld-Nutzlasten brauchen Hilfsverbunde | F1, F3 |
| **B16** | 130 | :385-386, :239 | `table` kennt genau ein `slot`-Wort und keine Parameter; und eine `invariant` im `table`-Rumpf hat keinen Namen fuer ihre eigene Tabelle | F1, F3, F6 |
| **B17** | 536 | :414, :434 | Ein `transition` schreibt **genau ein** `place`; `state` nennt den Typ nicht, ueber dem es steht. „`caller` und `reply_owner` nie halb gesetzt" ist damit wieder ein Kommentar | **F3 toedlich** |
| **B18** | 705 | :426-435 | `device` kennt keine Phasen und `regdecl` eine Klasse je Register — „`used` gehoert dem Geraet" ist nicht typisierbar. Betrifft eine bezahlte Falle (wiederverwendete Virtqueue) | F4 |
| **B19** | 716 | :468, :598 | `publishes` sitzt am Atomic (das nach B2 unerreichbar ist), nicht am Geraeteregister. Die fuenf Barrieren des virtio-Pfads haben keinen Traeger | F4 |
| **B20** | 713 | :139, :388 | `wrapping` gehoert an `slottype`, nicht an `intty`. Ein umlaufendes REGISTER (avail-Index, laut Spezifikation bei 65536) ist nicht schreibbar | F4 |
| **B21** | 949 | :468, :600 | Kein atomares Lese-Aendere-Schreibe: `accumulates max/min/+` fehlt. 213 Fundstellen im Baum, davon 19 `fetch_max`/`fetch_min` | F6 |
| **B22** | 1004 | :95 | Zeichenketten sind einzeilig (`char` schliesst `newline` aus). Alle drei `claim`-Texte und zwei `assume`-Texte sind mehrzeilig | F2, F6 |
| **B23** | 366 | :430 | Eine Klasse je Register kann ein gemischtes Register nicht ausdruecken. VT-d `FSTS` ist w1c in 7:0 und r in 15:8 — `class w1c` macht `FRI` unlesbar | F2 |
| **B24** | 383 | :146, :393 | `bitpos` sagt nichts ueber Bitlagen jenseits von 64 und nichts ueber das Zusammenwirken mit `endian`. Der VT-d-Fault-Satz besteht aus zwei Woertern | F2 |
| **B25** | 429 | :139 | `intty in range` ist ein Intervall, keine Wertemenge — ein Feld an die Werte eines `reason` zu binden geht nur, wenn die Codes zufaellig zusammenhaengen | F2 |
| **B26** | 395 | :430-435 | `regdecl`s `requires` hat keinen benannten Ausgang (`else QueueTooBig`), und es gibt keinen Platzhalter fuer den Vorzustand einer `transition` (`any -> 0`) | F2, F4 |
| **B27** | 831 | :266-274 | `prim fn` hat keinen `abi`-Block: `arch` gibt es, die Registerbelegung nicht. Der Ort, an dem 168 `asm!`-Stellen zusammenlaufen sollten, hat keinen Inhalt | F5 |
| **B28** | 251 | :320 | Kein Platzhalterbinder in `match`-Armen. Zehn Varianten ohne Nutzlastgebrauch brauchen zehn tote Namen | F1 |
| **B29** | 245 | :588, :607-609 | Relationale Vorbedingung: `refcount -= 1` faellt nur ueber eine Invariante, die nach B13 gar nicht schreibbar ist. Der Streitfall der Trennlinie, an einem echten Fall | F1 |
| **B30** | 973 | :340 | `touches` nimmt eine `efflist` ohne Klammern, `effects` ueberall sonst mit. Beide Vorlagen schrieben `touches { … }` | F4, F6 |
| **B31** | 228 | :235-236, :200 gegen :292 | `old(place)` haengt unter `atompred`, nicht unter `primary` — es kann als Praedikat fuer sich stehen, aber in keinem Ausdruck vorkommen. **Keine Differenzaussage („nachher gegen vorher") ist schreibbar**, und die Datei gibt in ihrem eigenen `delete_leaf`-Beispiel eine an | F1, und jede `ensures` mit `old` |

## Was in den Scratchpad-Dateien GAR NICHT ausgeschrieben ist

Damit niemand daraus schliesst, es sei geprueft:

* **Der Scheduler.** Kein Fragment, in keiner der fuenf Dateien. Es gibt Prosa zu `SCHEDS`,
  Sperrraengen und der Grund-Menge (Z24) — aber keine Zeile Gabbro. `forever … per_pass … progress
  timer_tick_arrives` in `SYNTAX.md`:363-368 ist ein Beispiel der Grammatik, kein Fragment.
* **Die MMU/Seitentabellen.** Ausdruecklich zurueckgestellt (`syntax-entwurf.md`, VII.3), mit der
  Begruendung, dass ein PTE zugleich Zeiger und Bitfeld ist — das ist der offene Punkt
  `SYNTAX.md`:591-593 und nicht mit einem Fragment beantwortet.
* **Der Lader / `SYS_LOAD` / die Verifizierung.** Es gibt eine einzelne Zeile
  (`prim fn seal_code(…)`, `syntax-entwurf.md`:1716) und die Aussage, dass W^X damit ein Axiom
  wird — kein Fragment.
* **GPT/FAT-Parser.** Zwei `format`-Bloecke im Entwurf (`syntax-entwurf.md`:128-144), die den
  Kopf, aber nicht das Lesen abbilden; `bounded_by` darin ist kein Wort der Grammatik, und
  `[GptEntry; GptHeader.entry_count]` verlangt eine **Laufzeit**laenge, wo `array` (:142) einen
  `constexpr` fordert. Nicht als Fragment gefuehrt, weil kein Rumpf dazu existiert.
* **Der Checkpoint (Z4).** Kommt in keiner der Dateien vor.


---

## F7 — Lader/Bringup: die Bootstrecke mit `BootPhase` als Wert

**Geschrieben 2026-08-16** gegen `kernel/src/main.rs:143-310` (`../caprock-messbasis`,
`a1bf707`). **Das Fragment entscheidet die Klempnerei-Klasse *Phase*** — Vorab und Tor
(`k = 5`) stehen in `MESSUNGEN.md`, Commit `27805bd`.

Die Vorlage traegt ihre Reihenfolge **in Kommentaren**. Sieben Stellen, jede mit dem Satz,
der sie erklaert:

| # | Fundstelle | was sie sagt | Bedingung |
|---:|---|---|---|
| 1 | `main.rs:144`/`:151` | *„Vor der MMU sind Atomics/Spinlocks nicht wohldefiniert"* | Einkern + Reihenfolge |
| 2 | `main.rs:213` | *„Cap-Tabellen VOR dem ersten Cap"* | Reihenfolge |
| 3 | `main.rs:222` | *„IPC-Tabellen VOR dem ersten Endpoint"* | Reihenfolge |
| 4 | `main.rs:251` | *„erst das Autoritaetsdokument melden, dann den Root-Task starten"* | Reihenfolge |
| 5 | `main.rs:256` | *„der Verifizierer MUSS vor dem Root-Task stehen"* | Reihenfolge |
| 6 | `main.rs:303` | AP-Eintritt: *„erst danach Atomics/Konsole gueltig"* | Einkern |
| 7 | `caprock-slab/src/lib.rs:173` | *„nur beim Boot aufrufen, bevor andere Kerne"* | Einkern |

> **Und Nr. 4 ist ein bezahlter Fehler genau dieser Klasse:** *„Genau diese Zeile fehlte auf
> ARM — hier lief der Manifest-Pfad ungeprueft mit."* Die Reihenfolge stand als Kommentar in
> einer Architektur und **fehlte in der anderen**. Kein Werkzeug konnte es sagen.

```gabbro
module caprock::bringup {

-- Die Marke ist LINEAR: sie entsteht einmal, wandert durch die Strecke und wird am Ende
-- verbraucht. Ein Weg, der sie fallenlaesst, ist ein Bootpfad, der nie fertig wird; einer,
-- der sie verdoppelt, sind zwei Kerne, die beide glauben, sie booten allein.
linear ghost type BootPhase;

-- `roh` heisst: vor der MMU. Atomics sind hier nicht wohldefiniert, also ist die Konsole
-- sperrfrei -- und das ist eine EIGENSCHAFT DER PHASE, nicht des Geraets.
extern fn melde_roh(text : ptr<code, r> Text) -> u32
    requires  Held(PHASE_ROH)
    effects   { reads text } costs <= 64 ops;

-- «B37» -- DER BEFUND DES FRAGMENTS. Die Marke traegt die Reihenfolge, aber sie traegt sie
-- als LINEARITAET, nicht als ORDNUNG: `mmu_an` verbraucht die rohe Phase und gibt die
-- gewoehnliche zurueck. Damit ist „vor der MMU" und „nach der MMU" unterscheidbar --
-- **aber „Cap-Tabellen vor dem ersten Cap" ist es nicht**, denn beide liegen in derselben
-- Phase. Fuer die vier Reihenfolgezwaenge INNERHALB einer Phase braucht es entweder je
-- eine eigene Marke (dann waechst der Wortschatz mit jedem Bootschritt) oder eine
-- Ordnung auf Marken -- und die gibt es nicht.
extern fn mmu_an(p : BootPhase) -> BootPhase
    effects { consumes p, writes mmu } costs <= 4096 ops;

extern fn cap_tabellen(p : BootPhase) -> BootPhase
    effects { consumes p, writes caps } costs <= 2048 ops;

extern fn ipc_tabellen(p : BootPhase) -> BootPhase
    effects { consumes p, writes eps } costs <= 2048 ops;

extern fn autoritaet_melden(p : BootPhase) -> BootPhase
    effects { consumes p, reads manifest } costs <= 512 ops;

extern fn verifizierer_starten(p : BootPhase) -> BootPhase
    effects { consumes p, writes faeden } costs <= 4096 ops;

-- Der Root-Task VERBRAUCHT die Marke endgueltig: danach ist der Bootzustand vorbei, und
-- kein Pfad kann noch etwas tun, das nur waehrend des Boots erlaubt war.
extern fn root_task_starten(p : BootPhase)
    effects { consumes p, writes faeden } costs <= 8192 ops;

impl fn hochlauf(p : BootPhase)
    effects { consumes p, writes mmu, writes caps, writes eps, reads manifest,
              writes faeden }
    costs   <= 32768 ops
{
    let p1 = mmu_an(p);
    let p2 = cap_tabellen(p1);
    let p3 = ipc_tabellen(p2);
    let p4 = autoritaet_melden(p3);
    let p5 = verifizierer_starten(p4);
    root_task_starten(p5);
}

}
```

**Urteil: die Marke TRAEGT — an sieben Stellen, gegen ein Tor von fuenf.**

Und der Ertrag ist nicht die Zahl, sondern **was sie NICHT traegt**: die Marke macht
*„vor der MMU"* von *„nach der MMU"* unterscheidbar, weil dort ein Verbrauch liegt. **Die
vier Reihenfolgezwaenge innerhalb einer Phase traegt sie nicht** — `cap_tabellen` vor
`ipc_tabellen` steht hier nur, weil ich es hingeschrieben habe. Der Uebersetzer sieht eine
Kette von Verbraeuchen und sagt nichts ueber ihre **Reihenfolge**.

> **«B37»:** Linearitaet erzwingt *genau einmal*, nicht *in dieser Ordnung*. Fuer die
> Reihenfolge braeuchte es je Schritt eine eigene Marke — dann waechst der Wortschatz mit
> jedem Bootschritt — oder eine **Ordnung auf Marken**, und die gibt es nicht.
