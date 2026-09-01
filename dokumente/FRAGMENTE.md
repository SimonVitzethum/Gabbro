# Gabbro — the written-out fragments

**Six fragments from six Caprock areas, held against today's grammar.**
As of 2026-08-14. **No compiler reads this.** None of it is compiled, run or measured — it is
text that was checked against [`SYNTAX.md`](SYNTAX.md), production by
production.

> **That sentence has been false since the compiler existed, and it is the one line of this file
> that speaks about TODAY rather than about 2026-08-14.** `crates/gabbro-check/tests/korpus.rs`
> cuts every ```gabbro block below and asserts that each refusal is a named code; `gabbro
> fragmente dokumente/FRAGMENTE.md` reports `Uebersetzungseinheiten: 10 von 10 ohne Fehler
> (100 %)` — that **is** gate P2; `zaehle-bereichspflichten.py` measures over this file. *The
> fragments are read, and the balance below was drawn before anything read them.* Everything
> after this note is a record of 2026-08-14 and stays untouched, including the findings that
> have since been closed.*

Until today `SYNTAX.md` carried, under the open points: *"Not a single written-out fragment
lies in the folder."* The fragments lay in the scratchpad of two earlier sessions and were written
against **older** versions of the grammar. This file brings them in, catches them up and
delivers a verdict per fragment.

## What has changed since — and what that moved in the fragments

| Change | Effect on the fragments |
|---|---|
| *"keeping"* is gone, `mirrors <reg> from <reg>;` once per device | **closes** the most expensive gap of the VT-d fragment (trap 4) |
| `publishes` is mandatory, `publishes nothing` exists | **closes** two of the three findings of the test-scaffold fragment |
| `relaxed` exists | **closes** the third |
| `old`, `offset_into`, `never` are real productions | `old(...)` in `delete_leaf` now carries |
| `loop … variant` is gone; `traverse`/`retry`/`forever` | `retry` carries the virtio poll unchanged; `forever` does **not** carry the service loop (no exit) |
| `costs` counts operations, not cycles | every `costs` line converted — and `SYNTAX.md` itself not (**«B4»**) |
| `bitpos` as a range `@[33:24]`, `bank … at expr` | **closes** the three largest VT-d gaps (multi-bit fields, runtime-computed register location) |

**The yield is asymmetric, and that is the news:** the device side has closed considerably over
the last two versions, the **expression** side has not. Of the 31 findings below, 7 sit in
`SYNTAX.md` itself (contradictions between prose, example and EBNF), and the heaviest of them
(**«B2»**) makes **every atomic, every lock and every critical section in all six fragments
unwritable** — not because the constructs are missing, but because they are **not reachable** in
the EBNF.

## How it was checked

1. **Vocabulary:** every word that is not an identifier must stand in the closed table
   (`SYNTAX.md` §Wortschatz). Units after `costs`/`bounded` are free identifiers —
   which is why no guardian can see whether `ops` or `cycles` stands there (**«B4»**).
2. **EBNF:** every line against its production, with the line number in `SYNTAX.md`.
3. **Reachability:** machine-recomputed, which of the 103 rules are reachable from `program`.
   Result: **three load-bearing rules are not** (`atomicdecl`, `lockdecl`, `lockstmt`),
   plus the two lexical ones (`comment`, `newline`), which are allowed to be. `pruefe-syntax.sh`
   checks **closure** (no used non-terminal without a definition) — the opposite direction,
   **reachability**, it does not check, and that is exactly where the find sat.
4. **What is not writable stands as a comment `-- «Bnn»` in the line** instead of being smoothed
   away. A fragment that only passes because the inconvenient line is missing is not a
   result.

## Balance

| | |
|---|---|
| Fragments | **6** from 6 areas (cap space · VT-d · IPC · driver · userspace · test scaffold) |
| **fits unchanged** | **0** |
| **fits with findings** | **4** (F1 cap space, F2 VT-d, F4 driver, F6 test scaffold) |
| **does not fit** | **2** (F3 IPC fastpath, F5 service loop) — both fail on a *load-bearing* statement, not on trimmings |
| Findings | **31**, of them **7** in `SYNTAX.md` itself |
| Findings that reopen a Caprock trap paid for by name | **5**: B11 (D0, nameless exit) · B18 (reused virtqueue) · B19 (arch-neutral barrier) · B21 (the counter that only grows) · B26 (refuse instead of interpret) |

**The two "does not fit" are the yield of this round.** F3 fails because a `transition` writes
**exactly one** place — the reply obligation (`caller` and `reply_owner` together) was the
reason the fragment was written in `state` form at all. F5 fails because
`forever` has **no exit**: the D0 lesson ("a nameless exit from the server loop cost
ten days") is not expressible in today's grammar, because there is no exit
at all.

---

# F1 — Cap space: `delete_leaf`, `unlink`, `revoke`

**Origin (Rust original):** `crates/caprock-cap/src/space.rs:1062` (`delete_leaf`), `:1044`
(`unlink`), `:991` (`release_slot`), `:619` (`revoke`); `crates/caprock-cap/src/object.rs`
(`ObjectKind`).
**Draft in the scratchpad:** `delete_leaf.gabbro` (138 ll.), `syntax-entwurf.md:1063-1243`.

**Caught up:** `module x;` → `module x { … }` (`moduledecl` demands braces, SYNTAX.md:113) ·
`use a::{b,c}` → three `usedecl` (:114 knows no brace list) · `held(CAPS)` → `Held(CAPS)`
(§2 carries `linear ghost type Held(Lock)`) · `costs <= 200 cycles` → `<= 200 ops` · `type Gen = u32
wrapping;` drops out, `wrapping` belongs on the slot (:388) · second table `objects { … }` **inside**
the `table` → its own `table CapObjects` with `index into CapObjects` · slot fields with a trailing
comma (:386) · `tagged ObjectKind : u8 { … }` → `tagged type … = { … }` (:147) · `invariant` with
`cost` and `runs` (:389, previously left out).

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

**Verdict: fits with findings** — «B1», «B2», «B10», «B13», «B14», «B15», «B16», «B28», «B29», «B31».

The body carries: `unlink` stands line for line, `delete_leaf` loses the catch-all branch over
ten `ObjectKind` variants (in Caprock **five** variants have been added since it was laid down —
each would silently have fallen into `_ => {}`), and `revoke` shrinks from 26 body lines to 4,
because `by consuming` carries termination and leafness. **What does not carry is the bookkeeping itself:**
`refcount_matches` is unformulable after «B13», and `refcount -= 1` hangs on exactly that.

**What the proof part needs — and that is NOT a finding.** For this fragment a second part lies in
the scratchpad (`delete_leaf.beweis`, 7,2 KB): what a human would **additionally** have to
write down for the obligations to go through. It needs `ghost let`, `assert … by { … }`, `lemma …
requires … ensures … { induction over the slot table }` — and **none** of it exists. That is
not a hole but the line drawn: `SYNTAX.md`:567 lists *"hand-written lemmata"*
explicitly under what does not exist, and :253-259 states the price for it — there is no
emergency exit. **The proof part is thereby the measurement of that price on a real case:** the
preservation of `kind_zeigt_zurueck` by `unlink` splits into four cases, and Gabbro has no
form in which to conduct them. Either the property falls out of the construction, or it falls
out of the language.

---

# F2 — VT-d: the remapping unit as a `device`

**Origin:** `crates/caprock-hal/src/x86_64/vtd.rs:26-32` (register locations), `:42-52`
(`GCMD_STATE_MASK` — trap 4 literally), `:442` (`frr_off`), `:451` (`read_frr`), `:236-247`
(the state bits on the command write).
**Draft in the scratchpad:** `vtd.gabbro` (155 ll.).

**Caught up — and here the new grammar helped most:** the draft carried
**seven** gaps, **four** of them are closed. Multi-bit fields (`ND`, `SAGAW`, `MGAW`, `FRO`,
`NFR`, `MAMV`, `IRO`, `TTM`, `RTA`, the CCMD fields) now carry `@[hi:lo]` (`bitpos`,
SYNTAX.md:146). The fault-recording registers and the IOTLB registers lie at a **runtime-computed**
base and are writable as `bank … at CAP.FRO * 16 …` (:429). And the most expensive gap — *"there is
no form for: the state of this register is read out of that one"* — is `mirrors GCMD from
GSTS;` (:428). Multi-line strings in `assume` have been made single-line (`char` excludes
`newline`, :95).

**«B5»** In passing it shows: the explanatory paragraph on trap 4 (`SYNTAX.md`:453-458) still
speaks of *"keeping"* — a word the grammar no longer knows. The file explicitly
carries the writing rule that an abolished name stands in italics inside quotation marks and
**is no longer syntax** (:49-50); here it stands in backticks, i.e. as today's syntax. The
guardian cannot see it: it checks the vocabulary table against the **EBNF**, not against the
prose.

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
-- «B24» Zweitens: der Satz besteht aus zwei 64-Bit-Woertern -- **und seit dem 2026-08-18
-- steht das im Traegertyp statt im Kommentar.** Der urspruengliche Text las: *„Die Bitlagen
-- unten sind auf das jeweilige Wort bezogen, weil `format` keine Wortbreite kennt."* Sie
-- kennt sie: die Wortbreite IST der Feldtyp, und eine Lage jenseits davon bedeutet nichts.
--
-- **Nachgezogen am 2026-08-19, als `N007` in den Pruefer kam.** Sieben Stellen fielen, und
-- eine davon war ein Widerspruch INNERHALB dieser Datei: `typ` stand hier als `@[13:12]`,
-- das Register `FR_HI` derselben Einheit fuehrt `TYPE @[29:28]`. *Die zweite Zahl ist die
-- gemessene; die erste haette mit `sid @[15:0]` ueberlappt.*
format FaultRecordLo @version 1 endian little {
    input_addr : u64 @[63:12] where (input_addr & 0xfff) == 0,
}

format FaultRecordHi @version 1 endian little {
    sid    : u64 @[15:0],
    typ    : u64 @[29:28],
    grund  : u64 in 0x01 .. 0x0c @[39:32],
    at     : u64 @[61:60],
    f_bit  : u64 in 1 .. 1 @63,
}
-- «B22-nah, eigener Fall» `where f_bit == 1` WEIST ein leeres Register AB, statt „leer" zu
-- MELDEN. Das ist der Unterschied zwischen Absage und Abwesenheit, und `format` kennt nur
-- die Absage. Im Rust-Original ist genau das der Unterschied zwischen „kein Fault" und
-- „Aufzeichnung nicht lesbar" (vtd.rs:451).

format Slpte @version 1 endian little {
    R    : u64 @0,
    W    : u64 @1,
    SNP  : u64 @11,
    ADDR : u64 @[63:12],
}

-- «B24» Der Kontexteintrag ist 128 Bit breit, und **die Entscheidung verweigert `@[66:64]`
-- ausdruecklich**: eine Lage liegt im eigenen Wort, `u64` hat die Bits 0 bis 63, also nennt
-- `@[66:64]` nichts. *Der Ausweg steht in derselben Zeile von `PFLICHTEN.md`:* zwei Woerter,
-- und der Schreiber nennt das zweite, statt dass der Erzeuger es raet.
format ContextEntryLo @version 1 endian little {
    P        : u64 @0,
    FPD      : u64 @1,
    SLPTPTR  : u64 @[63:12],
}

format ContextEntryHi @version 1 endian little {
    AW       : u64 @[2:0],
    DID      : u64 @[23:8],
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

**Verdict: fits with findings** — «B23», «B24», «B25», «B26».

**That is the best result of the six.** Of the draft's seven gaps four are shut, and the
most expensive of them was the x86 version of trap 4: `mirrors GCMD from GSTS;` is **one line**
against a constant plus eleven lines of comment plus two sites done by hand
(`vtd.rs:52`, `:236`, `:247`). What remains is the register-class finding («B23») — and it is
not cosmetic: it makes unreadable the very field with which the driver finds the fault record.

---

# F3 — IPC: the fastpath `Endpoint::call`

**Origin:** `crates/caprock-ipc/src/lib.rs:611` (`call`), `:335` (`caller`); D11 sits in the
overflow branch of the sender queue.
**Draft in the scratchpad:** `syntax-entwurf.md:1348-1456`.

**Caught up:** `state X over Y` → `state X` (:414 knows no `over`) · `Some(x) -> { }` →
`Some(x) => { }` (:320) · `costs … cycles` → `ops` · `over e.receivers` → `over queue e.receivers`
(:242) · `Queue(ThreadId, QUEUE_CAP)` → monomorphic struct `TidQueue`.

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

**Verdict: does NOT fit** — «B17» is lethal, plus «B6», «B8», «B9», «B10», «B12», «B15».

The reasoning is not a matter of taste: the fragment was written to show that Caprock's
comment *"`caller` and `reply_owner` are always set and cleared together"* becomes in
Gabbro a **derivation instead of a promise**. With a `transition` that writes one place,
it stays a promise — and between the two assignments stands a state in which
`antwortpflicht_paarig` is violated and which no construct describes. On top of that comes «B10»: the
fastpath **changes its behaviour** if one rewrites it onto `traverse` without an exit.
**Two load-bearing statements, both gone.** What carries is D11 — and that is remarkable enough
to name: `let … else` forces the failure branch, a silent 33rd sender is not
writable.

**Three promises of the draft I did NOT take over, and the reason is not a grammar question.**
`syntax-pruefung-teil2.md` (G1–G3) held them against `crates/caprock-ipc/src/lib.rs:620-656`:

* `ensures e.caller is Some(cl) => cl == current_id(ops, core)` is **false**, not merely
  unproven. If a second thread B calls while the rendezvous with A is open, B lands in the
  `None` branch (`:652`), `caller` stays `Some(A)` — the promise claims `A == B`. That is exactly
  the state for which `senders` exists at all.
* `msg_copied` is declared, **counted** into its own metric and hangs on **no**
  `ensures`. The only functional property of a fastpath — *the message has arrived* — gates
  nothing, while `transfer(f, …)` stands beside it without any postcondition. Literally the
  paid-for trap *"a negative test can secure a property nobody uses"*, one
  level up.
* The `effects` names `locks SCHEDS[core]`, but the cross-core branch additionally takes the lock
  of a **foreign** core (`unblock`). Above it therefore says `locks SCHEDS` without an index — that
  is evaded, not solved.

**The lesson from it does not belong to the grammar but to the bookkeeping over it:** a
metric formed out of **unchecked promises** rewards the false promise, because it is
short.

---

# F4 — The driver: virtio transport, ring, buffer ownership

**Origin:** `crates/caprock-virtio/src/lib.rs:88-90` (register locations), `:334` (`publish`),
`:363` (`poll_used`), `:494-499` (`QUEUE_SIZE` as a foreign number), `:533` (the status word
assembled by hand), `crates/caprock-virtio/src/owned.rs` (buffer ownership).
**Draft in the scratchpad:** `grammatik-v3.md:112-274`.

**Caught up:** `where Self <= QMAX else QueueTooBig` → `requires Self <= QMAX` (`regdecl`,
:433) · `fields { … }` with a trailing comma (:432) · `retry` in the order of the production
(:343-348) · `touches { … }` → `touches` without braces (:340, **«B30»**).

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

**Verdict: fits with findings** — «B3», «B7», «B18», «B19», «B20», «B26», «B30».

The transport carries completely and takes trap 4 in its virtio version with it: the status word
is no longer assembled by hand. `retry` carries the poll word for word. **The ring does not
carry:** phases, a register class per phase and `publishes` on the device register are missing all
three, and together they carry two paid-for traps (reused virtqueue, barrier out of the address space).
The substitute via a linear ghost value carries the first — and needs «B3» to do it.

---

# F5 — Userspace: the service loop of `virtio-blk`

**Origin:** `programs/hardware/virtio-blk/src/main.rs:255` (`run`), `:317` (the loop),
`:418` (`OP_STOP`), `:92` (the op codes); `programs/libcaprock/src/lib.rs` (the syscall entry).
**Draft in the scratchpad:** `grammatik-v3.md:317-408`.

**Caught up:** `fn run … -> never` → `divergent fn` (`nevertype` is, per :138, the return type
of `prim`/`divergent`) · match arms as blocks (:320) · the `costs` unit.

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

**Verdict: does NOT fit** — «B11» is lethal, plus «B7», «B14», «B27».

What carries, carries well: `match` is exhaustive, so the `_ => reply(ST_BADOP)` branch no longer
exists in every server but **once**, in `decode_op`; the four `map_window` refusals are
forced through `let … else` instead of wished for. What does not carry is the **form** of the program:
a service is a loop that waits on an endpoint and must be able to leave it **by name**.
`forever` exists, an exit does not — and `retry until pred` is the wrong construct
(it repeats **until** `pred` holds; here it is to end **on** `pred`, and the body is
no retry attempt).

---

# F6 — Test scaffold: the stack high-water mark

**Origin:** `kernel/src/kstackmark.rs:145` (`unberuehrt`), `:192` (`messen`), `:199-203`
(`fetch_max`/`fetch_min`), `:372` (`marke`), `:432` (`MIND_MESSUNGEN`), `:445` (`urteil`),
`:281-283` (the calibration).
**Draft in the scratchpad:** `grammatik-v3.md:456-588`.

**Caught up — and here the new grammar closed two of the draft's three findings:**
`publishes nothing` now exists (:469), `relaxed` too (:470). The draft had carried both as a
gap: a pure counter was *"either contract-free or ungrammatical"*, and the
ordering set had left out the most frequent element with `Relaxed` (779 of 2257 measured
accesses) and taken in the never-used one with `SeqCst`.

```gabbro
module kernel::kstackmark {

reason Stackart {
    El0  = 0 "der 16-KiB-EL1-Stack eines EL0-Threads"
    Kern = 1 "der 64-KiB-Stack eines Kernel-Threads"
    exhaustive
}

const STACK_MAX : u64 = 65536;   -- nachgetragen 2026-08-15: benutzt, nie erklaert
type Bytes = u64 in 0 .. STACK_MAX;

-- **Nachgetragen 2026-08-19, wie `STACK_MAX` am 2026-08-15: benutzt, nie erklaert.**
-- Der Rumpf unten liest `s.worte`, `s.len` und rechnet `i * 8` -- ein Wort ist acht Bytes,
-- also traegt ein Stack von `STACK_MAX` Bytes `STACK_MAX / 8` Worte. **Die Zahl ist
-- ABGELEITET und nicht erfunden**; sie steht dreimal im Rumpf und stand nirgends.
--
-- *Ohne diese Zeile hat `elems of s.worte` keine Schranke, und «H2.1» kann nicht greifen --
-- nicht weil die Regel zu schwach waere, sondern weil der Ausschnitt seinen Traeger nicht
-- nennt.* Der Befund gehoert zum Ausschnitt, nicht zu Gabbro.
const STACK_WORTE : u64 = 8192;
type Stack = { worte : [u64; STACK_WORTE], len : Bytes, };

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
    -- **Berichtigt 2026-08-18, gefunden von `M109`.** Hier stand `unberuehrt <= s.len` --
    -- der FUNKTIONSNAME an der Stelle, an der `result` hingehoert. Gabbro hat das Wort;
    -- die Vorlage kam aus einer Sprache, in der der Name das Ergebnis bezeichnet.
    -- *Die Zeile stand seit dem Schnitt da und ist niemandem aufgefallen, weil `ensures`
    -- von keinem Pass gelesen wurde.*
    ensures  result <= s.len
    effects  { reads s }
{
    let mut i : u64 in 0 .. STACK_MAX = 0;
    -- «B30» `touches` nimmt eine `efflist` OHNE Klammern (:340), waehrend `effects`
    -- ueberall sonst geklammert ist. Die Vorlage schrieb `touches { reads s }`.
    traverse w of s over elems of s.worte by unvisited decreases (lenof(s.worte) - i)
        touches reads s
    {
        if w != MUSTER { return i * 8; }
        -- ~~Nachgezogen 2026-08-15: die Schranke faellt zwar aus der Domaene (die
        -- Traversierung laeuft ueber `s.worte`), **aber M1 sieht das nicht** -- der
        -- Zaehler ist eine gewoehnliche lokale Variable. Der `else`-Zweig kann nicht
        -- genommen werden und muss trotzdem dastehen.~~ *(2026-08-15)*
        --
        -- **Entfallen am 2026-08-19 mit «H2.1».** M1 sieht es jetzt: ein Zaehler, der in
        -- einer beschraenkten Traversierung hoechstens einmal je Durchgang waechst, erbt
        -- die Schranke seiner Domaene -- an der Zuwachsstelle `i <= c + (B-1)*k`.
        -- *Die Regel ist die einzige Ausnahme von `SPRACHE.md`:657 („Loops carry no facts
        -- inward"), und der Unterschied zwischen Ausnahme und Loch liegt in der Richtung:
        -- die Tatsache kommt nicht von aussen, sondern aus der Schleifenform selbst.*
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
        -- **Zweite Fassung, 2026-08-19 («H2.2»).** Hier stand:
        --
        --     return (g - f) + irq.tiefe_max + g / MIND_RESERVE_NENNER <= g;
        --
        -- `PFLICHTEN.md` fuehrte dazu die Pflicht *„`(g - f)` unterlaeuft nicht"* mit der
        -- Begruendung *„`f < g / N` gibt `f < g` nur ueber die Division; die V-Regeln rechnen
        -- nicht."* **Nachgerechnet: die Begruendung beschreibt den falschen Zweig.** Der
        -- Vergleich steht in einem `if`, das ZURUECKKEHRT -- auf dem Weg hierher gilt
        -- `f >= g / N`, eine UNTERE Schranke, und `g - f` braucht eine obere. Keine
        -- schaerfere V-Regel schliesst das.
        --
        -- Die Aussage ohne Subtraktion ist unter `f <= g` aequivalent und hat keine
        -- Unterlaufpflicht. **Die Pflicht war ein Artefakt der Schreibweise, nicht der
        -- Sprache** -- dieselbe Klasse wie `revoke` (200 zugesagt, 16 452 480 gerechnet):
        -- *ein Mensch hat den typischen Fall geschrieben statt die Schranke.*
        return irq.tiefe_max + g / MIND_RESERVE_NENNER <= f;
    }
    floor    gemessen_tod >= MIND_MESSUNGEN, groesse >= 1, irq.n >= 1
    counterprobe "Fuellung ausgehaengt" expects erschoepft_waechst
}

}
```

**Verdict: fits with findings** — «B2», «B6», «B7», «B14», «B21», «B22», «B30».

**`check` itself would hit exactly:** the `measures` list **is** the report line (in the real code
there are three versions of the same list — a struct `Marke` with ten fields, the function that
fills it, and the formatting line); `floor` hits exactly the three speech tests that
`urteil()` conducts by hand; and `gates kstack` at the calibration is the linear chain that in the
real code stands as a voluntary first conjunct. **What does not carry is the measured quantity:**
without an atomic read-modify-write («B21») there is no high-water mark, and without `option` as a
type («B14») exactly the interpretation returns that `floor` is built against.

---

# The findings

**31 findings. 7 sit in `SYNTAX.md` itself** (B1–B6 and B31: contradictions between EBNF, prose
and its own examples), **24 are gaps in the means of expression**. Column "Line" is the line **in
this file** at which the finding is anchored; column "SYNTAX.md" names the affected
production.

> **Two things about this table's own description are no longer true, and they are named here
> rather than repaired.**
>
> **The count.** The file carries **38** distinct `«Bnn»`; seven of them have no row — B32, B33,
> B34 (in the frozen F4 comments) and B37–B40 (the F7–F10 verdicts of 2026-08-16). *31 was right
> on 2026-08-14 and has been a count of the table rather than of the findings ever since.*
>
> **The `Line` column.** Twenty-two of the thirty-one line numbers no longer point at their
> anchor — the file has grown above them. **They are deliberately not re-derived.**
> [`HISTORIE.md`](HISTORIE.md) books exactly this as a fallen version (*"a location note in
> running text — stale at the first insertion above it. Statements about **order** hold, line
> numbers do not"*), and `korpus.rs` was re-anchored to content for the same reason on
> 2026-08-15. *Re-deriving the column would restart the rot clock; anchoring on `«Bnn»` or
> dropping it is the folder-consistent fix, and that is a decision, not a translation.*

| # | Line | SYNTAX.md | Finding | hits |
|---|---|---|---|---|
| **B1** | 171 | :266-274 against :287 | `spec fn … = pred;` the file uses this form itself, `fndecl` allows only `block \| ";"`. Through a `block` a quantifier is not reachable, because `pred` does not hang under `expr` | F1, F3, every `spec fn` |
| **B2** | 124 | :111-112, :313-314 | `atomicdecl`, `lockdecl`, `lockstmt` are defined and **not reachable** from `program`. Machine-recomputed: 103 rules, 3 unreachable | F1, F3, F4, F6 — every lock, every atomic |
| **B3** | 744 | :135-136 against :162-167 | `linear ghost type Held(Lock);` writes a type list where `params` demands `ident ":" typeexpr`. Four of its own examples, `Held` in every `requires` | all six |
| **B4** | 22 | :295, :366 against :580 | `costs <= 200 cycles` in the example against the decision "`costs` counts operations". The unit is a free identifier — no guardian can see it | all six |
| **B5** | 334 | :453-458 against :428 | The paragraph on trap 4 explains *"keeping"*, a word that no longer exists; the production is called `mirrors` | F2 |
| **B6** | 574 | :266-274 | No name for the return value in `ensures`. `old(place)` exists, a `result` does not | F3, F4, F6 |
| **B7** | 785 | :200 | No struct and no array literal in `expr`. A function therefore cannot produce a `structty`; tuple return and `reply(EP, [ … ])` fall with it | F4, F5, F6 |
| **B8** | 560 | :202 | No call through a `place`: `ops.current_id(core)` is not a `call`, although `fnptr` exists as a type | F3 |
| **B9** | 557 | :148 | `fnptr` carries no contract — the substitute for `&mut dyn SchedOps` loses exactly what it was there for | F3 |
| **B10** | 283 | :337-341 | `traverse` yields no value, there is no `break`. The search for the FIRST hit becomes the emptying of the whole set; an operation counter cannot be raised | F1 (`peak_revoke_ops`), F3 (fastpath) |
| **B11** | 862 | :350-354, :603 | `forever` has no exit; `leave`/`break`/`continue` do not exist. The D0 lesson ("a nameless exit from the server loop") is not expressible | **F5 lethal** |
| **B12** | 549 | :238-244 | No numeric-range domain (`forall i in 0 ..< MSG_WORDS`); and whether `slots of` binds an index or a slot is not laid down — both readings occur in the file | F1, F3, F6 |
| **B13** | 165 | :230-247 | No aggregation (`count`) and no cross-table domain in `pred`. `refcount_matches` — the bookkeeping of the capability system — is not formulable | F1 |
| **B14** | 162 | :137, :387, :316 | `option` exists only as a `slottype`, not as a `typeexpr`; and `let … else` demands a `call` on the right, so it does not unpack a `place` | F1, F5, F6 |
| **B15** | 111 | :137, :147, :150 | No type application: `Outcome(T,E)`, `Queue(T,N)` unwritable; `variants` takes exactly one `typeexpr` per variant, multi-field payloads need helper structs | F1, F3 |
| **B16** | 130 | :385-386, :239 | `table` knows exactly one `slot` word and no parameters; and an `invariant` in the `table` body has no name for its own table | F1, F3, F6 |
| **B17** | 536 | :414, :434 | A `transition` writes **exactly one** `place`; `state` does not name the type it stands over. "`caller` and `reply_owner` never half set" is thereby a comment again | **F3 lethal** |
| **B18** | 705 | :426-435 | `device` knows no phases and `regdecl` one class per register — "`used` belongs to the device" cannot be typed. Concerns a paid-for trap (reused virtqueue) | F4 |
| **B19** | 716 | :468, :598 | `publishes` sits on the atomic (which after B2 is unreachable), not on the device register. The five barriers of the virtio path have no carrier | F4 |
| **B20** | 713 | :139, :388 | `wrapping` belongs on `slottype`, not on `intty`. A wrapping REGISTER (avail index, per the specification at 65536) is not writable | F4 |
| **B21** | 949 | :468, :600 | No atomic read-modify-write: `accumulates max/min/+` is missing. 213 sites in the tree, of them 19 `fetch_max`/`fetch_min` | F6 |
| **B22** | 1004 | :95 | Strings are single-line (`char` excludes `newline`). All three `claim` texts and two `assume` texts are multi-line | F2, F6 |
| **B23** | 366 | :430 | One class per register cannot express a mixed register. VT-d `FSTS` is w1c in 7:0 and r in 15:8 — `class w1c` makes `FRI` unreadable | F2 |
| **B24** | 383 | :146, :393 | `bitpos` says nothing about bit positions beyond 64 and nothing about the interplay with `endian`. The VT-d fault record consists of two words | F2 |
| **B25** | 429 | :139 | `intty in range` is an interval, not a set of values — binding a field to the values of a `reason` works only if the codes happen to be contiguous | F2 |
| **B26** | 395 | :430-435 | The `requires` of `regdecl` has no named exit (`else QueueTooBig`), and there is no placeholder for the prior state of a `transition` (`any -> 0`) | F2, F4 |
| **B27** | 831 | :266-274 | `prim fn` has no `abi` block: `arch` exists, the register assignment does not. The place at which 168 `asm!` sites were meant to converge has no content | F5 |
| **B28** | 251 | :320 | No placeholder binder in `match` arms. Ten variants with no payload use need ten dead names | F1 |
| **B29** | 245 | :588, :607-609 | Relational precondition: `refcount -= 1` falls only via an invariant that after B13 is not writable at all. The contested case of the dividing line, on a real case | F1 |
| **B30** | 973 | :340 | `touches` takes an `efflist` without braces, `effects` everywhere else with them. Both drafts wrote `touches { … }` | F4, F6 |
| **B31** | 228 | :235-236, :200 against :292 | `old(place)` hangs under `atompred`, not under `primary` — it can stand as a predicate on its own, but cannot occur in any expression. **No difference statement ("after against before") is writable**, and the file states one in its own `delete_leaf` example | F1, and every `ensures` with `old` |

## What is NOT written out at all in the scratchpad files

So that nobody concludes from it that it has been checked:

* **The scheduler.** No fragment, in none of the five files. There is prose on `SCHEDS`,
  lock ranks and the reason set (Z24) — but not a line of Gabbro. `forever … per_pass … progress
  timer_tick_arrives` in `SYNTAX.md`:363-368 is an example of the grammar, not a fragment.
* **The MMU/page tables.** Explicitly deferred (`syntax-entwurf.md`, VII.3), on the
  grounds that a PTE is pointer and bitfield at once — that is the open point
  `SYNTAX.md`:591-593 and not answered with a fragment.
* **The loader / `SYS_LOAD` / the verification.** There is a single line
  (`prim fn seal_code(…)`, `syntax-entwurf.md`:1716) and the statement that W^X thereby becomes
  an axiom — no fragment.
* **GPT/FAT parser.** Two `format` blocks in the draft (`syntax-entwurf.md`:128-144) that map the
  header but not the reading; `bounded_by` in them is not a word of the grammar, and
  `[GptEntry; GptHeader.entry_count]` demands a **runtime** length where `array` (:142) requires a
  `constexpr`. Not carried as a fragment, because no body for it exists.
* **The checkpoint (Z4).** Occurs in none of the files.


---

## F7 — Loader/bringup: the boot path with `BootPhase` as a value

**Written 2026-08-16** against `kernel/src/main.rs:143-310` (`../caprock-messbasis`,
`a1bf707`). **The fragment decides the plumbing class *phase*** — advance protocol and gate
(`k = 5`) stand in `MESSUNGEN.md`, commit `27805bd`.

The original carries its ordering **in comments**. Seven sites, each with the sentence
that explains it:

| # | Site | what it says | Condition |
|---:|---|---|---|
| 1 | `main.rs:144`/`:151` | *"Before the MMU atomics/spinlocks are not well defined"* | single-core + order |
| 2 | `main.rs:213` | *"cap tables BEFORE the first cap"* | order |
| 3 | `main.rs:222` | *"IPC tables BEFORE the first endpoint"* | order |
| 4 | `main.rs:251` | *"first report the authority document, then start the root task"* | order |
| 5 | `main.rs:256` | *"the verifier MUST stand before the root task"* | order |
| 6 | `main.rs:303` | AP entry: *"only after that are atomics/console valid"* | single-core |
| 7 | `caprock-slab/src/lib.rs:173` | *"call only at boot, before other cores"* | single-core |

> **And no. 4 is a paid-for mistake of exactly this class:** *"Precisely this line was missing on
> ARM — here the manifest path ran along unchecked."* The order stood as a comment in
> one architecture and **was missing in the other**. No tool could say so.

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

**Verdict: the token CARRIES — at seven sites, against a gate of five.**

And the yield is not the number but **what it does NOT carry**: the token makes
*"before the MMU"* distinguishable from *"after the MMU"*, because a consumption lies there. **The
four ordering constraints within one phase it does not carry** — `cap_tabellen` before
`ipc_tabellen` stands here only because I wrote it down. The compiler sees a
chain of consumptions and says nothing about their **order**.

> **«B37»:** linearity enforces *exactly once*, not *in this order*. For the
> order one would need a token of its own per step — then the vocabulary grows with
> every boot step — or an **order on tokens**, and that does not exist.


---

## F8 — Scheduler: `Stale(T)` **carried refutably**

**Written 2026-08-16** against `kernel/src/system.rs` and `crates/caprock-sched/src/lib.rs`
(`a1bf707`). **The lock situation is quoted, not surveyed anew** — `MEM` is the leaf, `CAPS` is
the outermost, `SCHEDS[*]` lies between ([`AN-CAPROCK.md`](AN-CAPROCK.md), N1).

### The candidate and the counter-probe

`Stale(T)` was to carry the pattern that **replaces double acquisition**: select under lock A,
release, continue under B, **re-check the finding**. Measured: **five values cross a lock
boundary in the scheduler and are used afterwards under a different lock.**

| # | Site | Value | does anything carry it? |
|---:|---|---|---|
| 1 | `system.rs:1119` → `caprock-sched:842` | `tid` to `kill` | **`resolve(tid)` — revalidates.** Exactly the pattern |
| 2 | `system.rs:8325` | `tid` to `kill` | the same |
| 3 | `system.rs:1109` | `tid` from `current_id` | **COUNTEREXAMPLE** — see below |
| 4 | `system.rs:9104` | `caller` from `current_id` | the same counterexample |
| 5 | `system.rs:4943` | `bekommen` from `priority_of` | self-test path; the value is **reported**, not used |

### **The counterexample, and it is justified word for word**

`system.rs:1107-1109`:

> *"remember the tid of the terminating thread before the switch; **IRQs are masked in the trap →
> the current thread is stable across the short locks**."*

**The value crosses a lock boundary and still needs no revalidation** — not because
somebody was careless, but because a **different** promise carries it: the masking. A
`Stale(T)` that enforces revalidation would **make this path unwritable**.

> **«B38»: `Stale(T)` in its enforcing version is too strict.** Two of five measured
> transitions rest not on revalidation but on **interrupt masking** — and that
> is in Gabbro today `masks IRQ`, i.e. **already an effect**. The honest form would be
> not *"every continuation re-checks"* but *"every continuation re-checks **or** names
> what carries it instead"* — and that is no new token but a condition on an
> existing one.
>
> ### And the side condition belongs to it, otherwise the carrier is an escape hatch
>
> **Whoever invokes masking must BE in the masked state.**
>
> Without that coupling *"masking carries me"* would be exactly the assurance from **R15**
> that is satisfied as soon as the checker stays silent — a `masks IRQ` in the effect list says
> that the function masks, not that it **runs masked**.
>
> **And it is mechanically checkable, not merely formulable:** `entrydecl` carries
> `nested ( "never" | "masked" | "bounded" constexpr )` — the entry context says whether a
> path is reached masked. The condition thereby reads in full:
>
> > *A value that crosses a lock boundary loses its facts. The continuation re-checks
> > anew **or** names a carrier — and a carrier `masks IRQ` counts only if the
> > entry context carries `nested masked`.*
>
> **That is the same cut as with `H005`:** there the *strength* of the witness decides, here
> the *state* at entry. Both times the bare naming is not enough.

```gabbro
module caprock::sched {

const NKERNE  : u32 = 64;
const NFAEDEN : u32 = 1024;

type KernIdx  = u32 in 0 ..< NKERNE;
type FadenId  = u32 in 0 ..< NFAEDEN;

table Laufliste count NFAEDEN {
    slot { belegt : bool, kern : KernIdx, prio : u32 in 0 .. 255, }
}

lock SCHEDS protects { belegt, kern, prio } rank 2
    held <= 300 ops
    shared held <= 32 ops;

-- Der Fall, der TRAEGT: der Wert ueberquert die Grenze, und die Fortsetzung prueft neu.
-- `resolve` ist genau die Neuvalidierung; ohne sie waere `toeten` ein Rennen.
extern fn aufloesen(l : ptr<normal, r> Laufliste, t : FadenId)
    -> option index into Laufliste
    requires Held(SCHEDS, shared)
    effects  { reads l.slots } costs <= 8 ops;

impl fn toeten(l : ptr<normal, rw> Laufliste, t : FadenId, k : index into Laufliste) -> bool
    effects { reads l.slots, writes l.slots, locks SCHEDS }
    costs   <= 340 ops
{
    locks SCHEDS {
        -- **Die Neuvalidierung.** Der Faden kann zwischen Auswahl und Tat verschwunden
        -- sein; `aufloesen` sagt es, und der `match` zwingt beide Ausgaenge.
        match aufloesen(l, t) {
            Some(i) => { l.slots[i].belegt = false; return true; }
            None    => { return false; }
        }
    }
    return false;
}

-- «B38» -- DER FALL, DEN DIE ZWANGSFASSUNG UNSCHREIBBAR MACHT.
-- Der Wert ueberquert dieselbe Grenze und braucht KEINE Neuvalidierung, weil eine andere
-- Zusage ihn traegt: die Interruptmaskierung. `masks IRQ` ist in Gabbro bereits eine
-- Wirkung -- die Begruendung steht also schon in der Sprache, sie ist nur nicht mit der
-- Sperrgrenze verknuepft.
impl fn beenden(l : ptr<normal, rw> Laufliste, k : index into Laufliste) -> bool
    requires Held(SCHEDS)
    effects  { reads l.slots, writes l.slots, masks IRQ }
    costs    <= 16 ops
{
    l.slots[k].belegt = false;
    return true;
}

}
```

### Verdict: **`Stale(T)` in the proposed form is refuted**

**Three of five transitions carry the pattern; two refute its enforcing version.** And the
two are not exceptions but the **hottest path** — `exit_current` and the
IPC handover path.

> **What remains is not a construct but a condition:** a value across a lock boundary
> loses its facts — *the language already does that, the V rules die* — and the
> continuation must **either re-check or name what carries it instead**. The second
> exit is `masks IRQ`, and that one exists.

**New constructs: 0.**


---

## F9 — MMU/page tables: the entry that is pointer **and** bitfield

**Written 2026-08-16** against `crates/caprock-hal/src/x86_64/mmu.rs` (1 719 lines,
`a1bf707`).

### The measured core

The descent is **four-level** and reads two things out of **the same 64-bit number**:

```
mmu.rs:578   let e4 = PML4.0[((va >> 39) & 0x1ff) as usize];
mmu.rs:582   let e3 = table_mut(e4 & MASK)[((va >> 30) & 0x1ff) as usize];
mmu.rs:589   let e2 = table_mut(e3 & MASK)[((va >> 21) & 0x1ff) as usize];
mmu.rs:596   let e1 = table_mut(e2 & MASK)[((va >> 12) & 0x1ff) as usize];
```

`e4 & MASK` is an **address**; `e4 & P`, `& RW`, `& US`, `& NX` are **rights bits** —
nine named ones, of them two (`A`, `D`) *"set by the HARDWARE, never by us"*.

**That was the finding that demanded the eighth domain** (`mappings of`), and it is answered with
`walk`/`embeds`.

```gabbro
module caprock::mmu {

const EBENEN   : u32 = 4;
const EINTRAEGE: u32 = 512;

opaque type Pa = u64;
type Idx   = u32 in 0 ..< EINTRAEGE;
type Ebene = u32 in 0 ..< EBENEN;

-- **Der Eintrag ist EIN Wort mit zwei Lesarten**, und `embeds` sagt welche. Ohne die
-- Zeile stünde die Adresse als blanke Zahl da, und `& MASK` wäre Konvention.
format Pte @version 1 endian little {
    roh : u64 embeds [51:12] scale 4096,   -- der Rahmen: Bits 51..12, mal 4096
}

-- Die neun Bits, einzeln benannt. `A` und `D` schreibt die Hardware -- sie stehen als
-- `reserved`, weil ein Schreiben von uns ein Fehler wäre.
device Seitentabelle(basis : Pa) at normal {
    reg EINTRAG : u64 @0x0 class rw fields {
        P @0, RW @1, US @2, PWT @3, PCD @4, A @5, D @6, PS @7, NX @63,
    }
}

-- `walk` erzeugt die Domäne `mappings of`: je Abbildung stehen `va`, `level` und
-- `index[level]` bereit. **Die vierstufige Kette wird damit EINE Traversierung**, und ihre
-- Schranke fällt aus der Deklaration statt aus einer Zählung im Rumpf.
walk Seitenabstieg levels EBENEN {
    node : [Pte; EINTRAEGE],
    down : roh when EINTRAG.PS == 0,
    leaf : EINTRAG.PS == 1,
}

-- Die Schranke faellt aus `levels` mal `node`-Laenge: 4 Ebenen zu 512 Eintraegen.
impl fn rechte_pruefen(w : ptr<normal, r> Seitenabstieg) -> bool
    effects { reads w }
    costs   <= 4096 ops
{
    traverse abbildung over mappings of w by unvisited
        touches reads w
    {
        if abbildung.level == 3 {
            return true;
        }
    }
    return false;
}

}
```

### Verdict: **fits — and the finding is what did NOT show up**

**New constructs: 0.** `embeds`, `walk` and `mappings of` already stood; the fragment
evidences them for the first time on the stretch they were designed for.

> **«B39» — the finding lies in the two bits the hardware writes.** `A` and `D`
> are set by the MMU **itself**, without software doing it. In Gabbro's effect computation that
> is a **writer no `effects` line names** — the frame statement *"only what
> stands there changes"* is **false** at this site, and not because of a gap
> in the checker but because the hardware is a participant.
>
> **The honest form is an assumption with a falsifier**, not an effect: *"the MMU
> sets `A`/`D`, nothing else"* — exactly the build that `assume … falsifier …` carries. With that
> the case belongs in the **axiom layer**, and it is one of the few that belong
> there, because they really are hardware.
>
> ### And the axiom alone does not suffice — it needs its exception rule
>
> **`A`/`D` are the GDT lesson on the page machinery.** Hardware writes into a structure that
> is otherwise thought of as `by ops`-like: a page table is exactly the carrier whose
> write sites one would like generated. **As soon as group `ops` reach the page machinery,
> the axiom collides with the write-rights promise** — the K condition demands that *all*
> write sites be generated, and the MMU is not a generated operation.
>
> **The exception must therefore stand at the declaration, not in running text:** which fields
> of a `walk` declaration are **hardware-writable** belongs in the declaration — the way
> `reserved` on a `format` field says that nobody writes it.
>
> ```gabbro
> walk Seitenabstieg levels EBENEN {
>     node : [Pte; EINTRAEGE],
>     down : roh when EINTRAG.PS == 0,
>     leaf : EINTRAG.PS == 1,
>     -- die Kandidatenzeile: `hardware A, D;`
> }
> ```
>
> **Without it the placement rule from `R001` is untenable at this site** — it says
> today *"an `ops` carrier lies in no `dma` space"*, and the reason is exactly this:
> a device writes past every grammar. **The MMU does the same, only in the `normal` space**,
> and `R001` does not see it.
>
> *Candidate, not a decision — and expressly one that burdens the convergence bet: it
> would be a new word.*


---

## F10 — Parser/checkpoint: the buffer nobody believes

**Written 2026-08-16** against `crates/caprock-dtb/src/lib.rs` (145 lines, `a1bf707`) —
the only parser of the kernel that reads **foreign bytes**.

### The measured core

`Dtb::parse` reads a magic word, then two offsets:

```rust
if be32(data, 0)? != MAGIC { return None; }
let off_struct  = be32(data, 8)?  as usize;
let off_strings = be32(data, 12)? as usize;
```

**Every access goes through `be32(data, n)?`** — a function that yields `Option`, i.e. checks the
length and gives `None` on overflow. **That is the range obligation, written out as
control flow**, and it stands at *every* access individually.

`format` takes exactly that off one's hands: **the reader checks the buffer length once at entry,
everything further is proven accesses.**

```gabbro
module caprock::dtb {

const MAGIE : u32 = 0xd00dfeed;

-- Der Kopf ist ein FORMAT: feste Breiten, ausgesprochene Bytereihenfolge, und die
-- `where`-Klausel bindet jeden Versatz an die Pufferlaenge. **Danach braucht kein
-- einziger Zugriff mehr eine Laengenpruefung.**
format DtbKopf @version 17 endian big {
    magie       : u32 where magie == MAGIE,
    gesamtlaenge: u32,
    off_struct  : u32 offset_into Self where off_struct + 4 <= lenof(Self),
    off_strings : u32 offset_into Self where off_strings + 4 <= lenof(Self),
}

-- Die Tiefe ist ein Zaehler, und die Zaehlerregel gilt: Schranke in der Deklaration UND
-- Pruefung vor der Rechnung. Ein DTB mit 2^32 verschachtelten Knoten ist kein Baum mehr,
-- sondern ein Angriff -- und die Schranke sagt das, statt es zu hoffen.
const MAXTIEFE : u32 = 64;
type Tiefe = u32 in 0 .. MAXTIEFE;

extern fn naechstes_token(k : ptr<normal, r> DtbKopf, pos : u32) -> u32
    effects { reads k } costs <= 4 ops;

impl fn kerne_zaehlen(k : ptr<normal, r> DtbKopf) -> u32
    effects { reads k }
    costs   <= 65540 ops
{
    let mut tiefe : Tiefe = 0;
    let mut zahl  : u32 in 0 .. 1024 = 0;

    retry lesen until naechstes_token(k, 0) == 9
        bounded 65536 ops
        progress token_verbraucht
        on_exceeded baum_unlesbar
        effects { reads k }
    {
        narrow tiefe to 0 ..< MAXTIEFE else { return zahl; }
        tiefe += 1;
    }
    return zahl;
}

extern fn baum_unlesbar() -> never effects { diverges } costs <= 0 ops;

-- **Der Zeuge, und bis 2026-08-18 stand er nicht da.** `progress` nennt eine Annahme mit
-- Falsifikator; ohne `assume` steht der Name in keinem Manifest. `S003` hat es gefunden.
assume token_verbraucht
    "Jeder Durchgang verbraucht mindestens ein Token, und ein DTB hat endlich viele."
    falsifier sonde_dtb_endlich;

}
```

### Verdict: **fits — and the finding is the place where the original already writes Gabbro**

**New constructs: 0.**

`be32(data, n)?` is already *"check, else refuse"* — the original has the rule, it only has
it **at every access individually** instead of once at entry. **That is the folder's cheapest
fragment finding**: `format` with `offset_into Self` and `where` replaces a
control-flow discipline that the author already sustains with a declaration that the
compiler sustains.

> **«B40» — and it goes against the folder.** The original checks **error-free over 145
> lines**, without a language and without a tool. *A parser that fulfils its range obligations
> individually anyway gains **brevity** from `format`, not **safety**.* The
> gain is real and it is **not the gain the folder promises** — and that
> needs saying, because `format` elsewhere (base rate: 5 formats, 0 errors) once already
> stood there without evidence.

---

# «F0» — der Gleitkommakorpus, und er hat sofort eine Planentscheidung gekippt

> **Gemessen 2026-08-18** an *Fraktaler 3* (Version 3.1), einem gleitkommaschweren Renderer:
> 52 Quelldateien, **479 `float`, 355 `double`, 37 `long double`**, 128 NaN/Inf-Stellen — und
> **kein `-ffast-math`** im Makefile eines leistungskritischen Programms.
>
> *Die Messbasis dieses Ordners (Caprock) hat null rechnende Gleitkommastellen. Ein Korpus für
> «F» muss also von außerhalb kommen, sonst entwirft man für eine vorgestellte Verwendung.*

## FF1 — Der Fluchttest. Vier der sieben Entscheidungen in einer Zeile.

```c
float t = float(arg(Z1)) / (2.0f * 3.141592653f);
if (Zz2 < ER2 || isnan(de.x) || isinf(de.x) || isnan(de.y) || isinf(de.y))
```

**Befund.** Der Programmierer schreibt die NaN-Prüfung **von Hand neben den Vergleich** — weil
`Zz2 < ER2` allein den Fall nicht abdeckt. *Das ist genau die Lage, die F1.3 beschreibt, und
hier steht sie als echter Code.* Dazu in derselben Umgebung: eine Klemmung
(`min(max(x, 0.), 1.)` — das ist `narrow`), eine Breitenmischung (`float` aus `double`,
ausdrücklich umgewandelt), zwei `log`-Aufrufe (libm, also die Axiomschicht) und ein
**inexaktes Literal** (`3.141592653`).

## FF2 — Die Genauigkeitsleiter. Sie beantwortet die `long double`-Frage.

```c
= { "none", "float", "double", "long double", "floatexp", "doubleexp", "softfloat"
#ifdef HAVE_FLOAT128
  , "float128"
#endif
};
```

**Befund, und er ist stärker als die Empfehlung, die er trägt.** In der Domäne, die
Extragenauigkeit *wirklich* braucht, ist `long double` **eine Sprosse von sieben** — darüber
liegen `floatexp`, `doubleexp`, `softfloat`, `float128`, alles Softwaretypen des Programms.

> **Wer mehr als f64 braucht, will keinen plattformabhängigen 80-Bit-Typ, sondern eine
> BENANNTE Genauigkeit.** Die Weigerung bei `long double` ist damit nicht Härte, sondern die
> Ablesung dessen, was echte Programme ohnehin tun.

## FF3 — Die Reduktion.

```c
progress_t a = 0;
for (count_t i = 0; i < count; ++i) { a += progress[1 + count + i]; }
```

**Befund.** Eine Summe über ein Feld — in Gabbro die Form, für die `accumulates` da ist. Über
Gleitkomma ist sie **reihenfolgeabhängig**, und `accumulates.monoid` ist unter der Prämisse
bewiesen, dass sie es nicht ist. *Der Korpus liefert damit den Bedarfsbeleg für `F004`: die
Weigerung ist nicht vorsorglich, sie trifft eine Form, die wirklich vorkommt.*

## FF4 — Die Literalmessung, und sie hat F1.5 gekippt

Alle 340 Gleitkommaliterale des Renderers gegen die Frage *„exakt darstellbar?"* gehalten
(`m/10^d` ist dyadisch genau dann, wenn `5^d` die Mantisse teilt):

```
340  Literale gesamt
287  exakt darstellbar   (84 %)   -- 0.0, 1.0, 2.0, 3.0, 0.5 …
 53  NICHT exakt         (16 %)   -- 0.6931471805599453, 6.283185307179586, 0.04045, 4.1
```

**Die geplante Regel hätte 53 Literale abgelehnt, darunter ln 2 und 2π.** Das ist keine
Härtung, das ist eine unbrauchbare Sprache: eine transzendente Konstante ist in *keiner*
binären Breite exakt, und ihre Dezimalform ist schon eine Näherung.

**Aber die Messung sagt auch, wo die Grenze wirklich liegt.** Die exakten 84 % sind
Strukturkonstanten; die inexakten 16 % sind **Näherungen an reelle Zahlen**. Die richtige
Regel verbietet also nicht das Inexakte, sondern das **stillschweigend** Inexakte:

```gabbro
const TAU : f64 = 6.283185307179586 rounded;
```

*Ein Wort, und es hat schon ein Geschwister im Ordner:* `u32 wrapping` sagt **der Überlauf ist
erklärt und darum kein Befund** — `rounded` sagt dasselbe über die Rundung. **Dieselbe Form,
dieselbe Begründung, und darum kein neues Muster.**

## Was F0 beigetragen hat

| | |
|---|---|
| **F1.3** bestätigt | die Handprüfung neben dem Vergleich steht als echter Code da |
| **F1.5 gekippt** | „exakt oder Absage" wäre unbrauchbar — die Regel heißt jetzt „erklärt oder Absage" |
| **`long double`** | die Weigerung ist eine Ablesung, keine Härte: echte Programme bauen eine Leiter |
| **F004** belegt | die Gleitkommareduktion kommt wirklich vor |
| **kein fast-math** | ein leistungskritischer Renderer verzichtet freiwillig darauf |

---

# «K2» — zwei Fragmente aus fremder Autorenlinie, geschnitten und gemessen

> **2026-08-18.** Die Zählung («K2» in `MESSUNGEN.md`) zählte Formen. *Der Unterschied
> zwischen „`format` gibt es" und „das Fragment geht durch" ist derselbe, den dieser Ordner
> schon einmal bezahlt hat* — also hier zwei geschnittene Fragmente, und was der Prüfer dazu
> sagt.

## K2-F1 — `setpriority`, und die zwei Sprungmarken

```c
		if (!uid_eq(uid, cred->uid)) {
			user = find_user(uid);
			if (!user)
				goto out_unlock;	/* No processes for this user */
		}
		…
out_unlock:
	rcu_read_unlock();
out:
	return error;
```

**Befund.** Zwei Sprungmarken, und die erste existiert **nur zum Freigeben**. In Gabbro gibt
es sie nicht: `locks { … }` nimmt und gibt auf jedem Pfad, und der Fehlerweg ist
`let … else`. *Die Marke verschwindet nicht, weil man sie umschreibt, sondern weil das
Problem nicht auftritt.*

**Verdikt: blockiert — `rcu_read_unlock`.** Und zwar nicht am `goto`, sondern an dem, was die
Marke freigibt.

## K2-F2 — `acct_get`, und `goto again` ist ein `retry`

```c
again:
	smp_rmb();
	rcu_read_lock();
	res = to_acct(READ_ONCE(ns->bacct));
	if (!res) { rcu_read_unlock(); return NULL; }
	if (!atomic_long_inc_not_zero(&res->count)) {
		rcu_read_unlock();
		cpu_relax();
		goto again;
	}
	rcu_read_unlock();
```

**Befund, und er hat drei Teile.**

**(1) `goto again` IST ein `retry`** — und in Gabbro trägt es eine Schranke und einen
benannten Überlauf. Das Original hat beides nicht: die Schleife ist **unbeschränkt**, und
wenn der Zähler nie freikommt, dreht sie für immer. *Der `on_exceeded`-Zweig ist kein Zusatz,
er ist die Stelle, an der aus einer Hoffnung eine Aussage wird.*

**(2) `rcu_read_unlock` steht DREIMAL** — einmal je Ausgang. Genau die Bauart, die
`locks { … }` unnötig macht; nur ist RCU keine Sperre, und Gabbro hat kein Wort dafür.

**(3) Und M1 fand beim ersten Lauf einen Überlauf, den das Original nicht prüft.**
`atomic_long_inc_not_zero` schützt gegen **null**, nicht gegen die obere Schranke:

```
die Zuweisung requires `u32 in 0 .. 65535`, the value has `u32 in 2 .. 65536`   -- M101
```

*Das ist die Zählerüberlaufklasse, und sie fiel aus einem fremden Fragment beim ersten
Rendern heraus.* Die Antwort steht in derselben Sprache — eine zweite Schranke im `if`, und
der Prüfer schweigt.

## Nachgebildet, RCU durch eine Sperre ersetzt: der Rest TRÄGT

```gabbro
module k2::acct {

const MAXVERSUCHE : u32 = 64;

table Konten count 256 {
    slot { zaehler : u32 in 0 .. 65535, }
}

lock NSLOCK protects { Konten } rank 10 held <= 400 ops;

extern fn cpu_relax() effects { pure } costs <= 1 ops;

impl fn holen(k : ptr<normal, rw> Konten, i : index into Konten) -> u32
    effects { locks NSLOCK, reads k.slots, writes k.slots }
    costs   <= 600 ops
{
    retry hole until k.slots[i].zaehler > 0
        bounded 512 ops
        progress halter_gibt_frei
        on_exceeded konto_verschwunden
        effects { locks NSLOCK, reads k.slots, writes k.slots }
    {
        locks NSLOCK {
            -- **Die Schranke, die das Original nicht hat.**
            if k.slots[i].zaehler > 0 && k.slots[i].zaehler < 65535 {
                k.slots[i].zaehler += 1;
            }
        }
        cpu_relax();
    }
    return 1;
}

assume halter_gibt_frei
    "Ein Halter gibt seinen Zaehler in endlicher Zeit frei."
    falsifier sonde_halter_haengt;

extern fn konto_verschwunden() -> never effects { diverges };

}
```

**0 Fehler, 0 Hinweise.** Das ist das eigentliche Ergebnis der ersten zwei Fragmente:
**ein einziges fehlendes Konstrukt blockiert beide, und der ganze Rest trägt** — Sperre,
Rang, Haltezeit, beschränkte Wiederholung, benannter Überlauf, Fortschrittsannahme mit
Falsifikator, Indexschranke.

> **Und es ist eine NACHBILDUNG, keine Übersetzung.** Die Tabelle ist erfunden, weil
> `struct bsd_acct_struct` nicht mitgeschnitten ist. Gemessen ist damit die FORM des
> Fragments und nicht sein Rumpf — derselbe Unterschied wie oben, eine Ebene tiefer.

---

# «K2» abgeschlossen — fünf Fragmente, und vier tragen ohne Rest

> **2026-08-18, nach RCU.** K2-F1 und K2-F2 waren an einem Konstrukt blockiert; es gibt es
> jetzt. Drei weitere sind dazugekommen, jedes für eine andere Klasse.

## K2-F1 — `setpriority`: **beide Sprungmarken entfallen**

```gabbro
observes TASKLIST {
    match nutzer_suchen(wer) {
        None    => { return 1; }
        Some(i) => { return Prozesse.slots[i].nice; }
    }
}
```

Im Original `out_unlock:` (gibt RCU frei) und `out:` (kehrt zurück). **Der Bereich endet mit
dem Block, der Fehlerweg ist `match`.** *Die Marken verschwinden nicht, weil man sie
umschreibt, sondern weil das Problem nicht auftritt.* — **0 Fehler.**

## K2-F2 — `acct_get`: trägt, und ist strenger als das Vorbild

Bereits gemessen: `goto again` ist ein `retry` mit Schranke und benanntem Überlauf, den das
Original nicht hat; und **M1 fand einen Zählerüberlauf**, gegen den nur `!= 0` schützte.

**Nach RCU bleibt ein Befund**, und er ist ein Befund über die Sprache: das Original benutzt
`atomic_long_inc_not_zero` — *ein atomares RMW ist seine eigene Wechselseitigkeit.* In Gabbro
ist `atomic` ein **Item und kein Slotfeld**, ein Zähler *im* Objekt also nicht atomar
deklarierbar. `H010` verlangt dort eine Sperre, die das Vorbild nicht braucht.

## K2-F3 — `sum_mthp_stat`: **dreizehn Zeilen werden eine Deklaration**

```gabbro
accumulates mthp_summe : u64 merge add per cpu 64;
```

Die Schleife über alle Kerne verschwindet, und die Reihenfolgeunabhängigkeit, auf die sie sich
stillschweigend verlässt, ist **bewiesen** (`accumulates.monoid`). — **0 Fehler.**

## K2-F4 — `pid_namespace`: der Fortschrittszeuge stand als KOMMENTAR da

```c
	/* Once all of the other tasks are gone from the pid_namespace
	 * free_pid() will awaken this task. */
	for (;;) { … schedule(); }
```

```gabbro
forever warten
    per_pass bounded 64 ops
    on_exceeded wachhund_schlug_an
    effects  { reads belegt }
    progress free_pid_weckt_uns
{ … }

assume free_pid_weckt_uns
    "Sind alle anderen Aufgaben aus dem Namensraum verschwunden, weckt `free_pid` diese hier."
    falsifier sonde_kein_aufwecken;
```

**Der Kommentar IST die Annahme.** Gabbro macht aus ihm eine Deklaration mit Falsifikator, und
dazu kommen die Schranke je Durchgang und der benannte Überlauf, die das Original nicht hat.
— **0 Fehler.**

## K2-F5 — `BUG_ON(addr >= end)`: die Zusicherung wird nicht geprüft, sie wird VERLANGT

Dreimal dieselbe Zeile in einer Datei. In Gabbro steht die Aussage im Typ, und die Beziehung
wird **einmal** geprüft, mit benanntem Ausgang.

**Und die Gegenprobe ist die eigentliche Messung:** nimmt man den Vergleich heraus, fällt die
Subtraktion.

```
`u32 in 0 .. 65535 - u32 in 0 .. 65535` leaves the width of the result type   -- M104
die Rueckgabe requires `u32`, the value has `u32 in -65535 .. 65535`          -- M101
```

> *Die Zusicherung wird nicht geglaubt, sie wird erzwungen* — und zwar zur Übersetzungszeit.
> Das ist die Zielgröße `BUG_ON`/`WARN_ON` **2034**, an einem Fall.

## Stand von «K2»

| | |
|---|---|
| **fünf Fragmente**, fünf Klassen | Sprungmarken · Wiederholung · per-Kern-Summe · unbeschränkte Schleife · Zusicherung |
| **vier tragen ohne Rest** | F1, F3, F4, F5 |
| **einer bleibt** | F2 — und der Rest ist ein Befund über die Sprache: kein Atomar im Slot |
| **drei Funde**, die kein eigener Korpus geliefert hätte | RCU als Klasse · der Zählerüberlauf · der Fortschrittszeuge als Kommentar |

**Und was das NICHT heißt:** fünf Fragmente sind keine Aussage über 64 000 Dateien. Es sind
Nachbildungen, keine Übersetzungen — die Strukturen sind erfunden, wo sie nicht mitgeschnitten
waren. *Gemessen ist die Form, nicht der Rumpf.*
