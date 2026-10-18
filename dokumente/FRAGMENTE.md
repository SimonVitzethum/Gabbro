# Gabbro — the written-out fragments

**Real code, written out in Gabbro, and what the language lacked to carry it.** Ten fragments
from ten Caprock areas, two corpora from outside (a floating-point renderer, a Linux kernel
tree) and a network stack. The point of this file is the *list of gaps* those programs found,
and which of them are closed today: §2. The ten Caprock fragments themselves are kept as they
were cut (2026-08-14 for F1–F6, 2026-08-16 for F7–F10); the completed, compilable copies live
in [`messung/fragmente/`](../messung/fragmente/).

> **Freeze sentence.** The ten ```gabbro blocks F1–F10 below are a report from 2026-08-14
> (F7–F10: 2026-08-16), and they stay untouched. A frozen excerpt is the yardstick; whoever
> edits it to make it pass moves the yardstick instead of discharging an obligation. Anything
> that needs a program that runs belongs in `messung/fragmente/F01.gab` … `F10.gab`, which
> carry exactly the lines that make the excerpts programs and say in their heads what was
> added. *Adding is allowed, leaving out is not*, and the retired `pruefe-emission` (2026-10-17; not guarded today) rejected a completed
> copy that lacked a frozen line.

## 0. Who reads this file mechanically

Do not reflow, reorder or rewrite the code blocks, and do not add a ```gabbro block or move the
heading «F0» without reading this table first. Rows marked *retired* name guardians removed on
2026-10-17 (see git history); they no longer read this file, but the block structure they relied on
is still what `korpus.rs` and `gabbro fragmente` read.

| Reader | What it needs from this file |
|---|---|
| `crates/gabbro-check/tests/korpus.rs` | cuts every ```gabbro block (`korpus::schneide`) and asserts that each refusal is a *named* code (the `BENANNT` list); the VT-d block (the one containing `device Vtd`) must stay completely clean (`f2_das_geraetefragment_bleibt_sauber`); `jeder_block_wird_gefunden` compares the cutter with the raw block count |
| `gabbro fragmente dokumente/FRAGMENTE.md` | the gate-P2 reader; reports per block `unit` (whole module) or `excerpt` (starts mid-form) |
| retired `zaehle-pflichten` | (retired) aborted unless there are **exactly 10** ```gabbro blocks before the heading that starts with `# «F0»`; blocks after it are the second corpus and are counted separately |
| retired `zaehle-bereichspflichten` | (retired) removed every `narrow` statement from this file's text, re-ran the checker and counted `M101`/`M104`; the corpus for the `narrow` count |
| retired `pruefe-emission` | (retired) cut blocks by a header string (`module caprock::bringup`, `module caprock::sched`, `module caprock::dtb`, `device Vtd`, `device Virtq`, `module kernel::kstackmark`, `module caprock::mmu`, `module caprock::cap::space`, `module programs::virtio_blk`) and checked that completed copies lose no frozen line |
| retired `zaehle-formate` | (retired) counted the format-version declarations written in this file's blocks next to the corpus |
| retired `pruefe-syntax` | (retired) the block text had not to contain the forbidden forms of `SYNTAX.md`, and the prose not to quote a retired German keyword |
| retired `pruefe-widerruf` | (retired) this file was exempt from the retraction scan (it quotes retracted sentences on purpose) |

Line numbers into this file that old comments quote (`FRAGMENTE.md:269`, `:692`, `:902`, …)
point at the layout of before the consolidation of 2026-10-17 and are stale; the content they
name is unchanged inside the blocks (the last section gives the shift per block).

## 1. How the corpus was built

1. **Vocabulary.** Every word that is not an identifier must stand in the closed table of
   `SYNTAX.md`.
2. **EBNF.** Every line is held against its production.
3. **Reachability.** Machine-recomputed which grammar rules are reachable from `program`; the
   first run found three load-bearing rules unreachable (`atomicdecl`, `lockdecl`, `lockstmt`,
   «B2»). The retired `pruefe-syntax` checked closure *and* that no rule is unreachable (189 rules
   booked in `SYNTAX.md`, 2026-10-17; not guarded today).
4. **What is not writable stays visible** as a comment `-- «Bnn»` in the line instead of being
   smoothed away. A fragment that passes only because the inconvenient line is missing is not
   a result.

The first six fragments carried 31 findings (7 of them in `SYNTAX.md` itself: contradictions
between prose, example and EBNF); F7–F10 added B37–B41. The asymmetric yield was the news: the
*device* side had closed over two grammar versions, the *expression* side had not.

## 2. The findings register — closed or open today

The «Bnn» ids are cited all over the checker, the tests and the instruments; they never get
renumbered. Status is read against `SYNTAX.md`, the corpus and the instruments named in the
last column (checked 2026-10-17; "not re-probed" means the status is the one booked in
the retired `PFLICHTEN` register or `SYNTAX.md` and was not run again today).

| # | Finding at the freeze | Status today | Evidence |
|---|---|---|---|
| B1 | `spec fn … = pred;` used by the file, rejected by its own EBNF | closed in practice | `spec fn` bodies with quantifiers stand in `beispiele/01`, `09`, `50` (0 errors); not re-probed |
| B2 | `atomicdecl`, `lockdecl`, `lockstmt` unreachable from `program` | **closed** | retired `pruefe-syntax`: every rule reachable |
| B3 | `linear ghost type Held(Lock);` unwritable | **closed** | retired `pruefe-notation` (`LUECKEN`) |
| B4 | `costs` unit a free identifier (`cycles` vs `ops`) | **closed** | grammar: `costs <= expr "ops"` is the only form |
| B5 | prose explains the retired word *keeping* | **closed** | the word no longer occurs in `SYNTAX.md` |
| B6 | no name for the return value in `ensures` | **closed** | `result`; retired `pruefe-notation` |
| B7 | no record or array literal in `expr` | **closed 2026-08-17** | labelled call `P(a: 1, b: true)`; *no* braced literal (76 corpus sites have a `{` right after an expression) |
| B8 | no call through a `place`; no producer of a function pointer | **closed** | `SYNTAX.md` «B8» productions; `fn(…)` types carry a contract (`N035`–`N037`) |
| B9 | `fnptr` carries no contract | **retracted — a false entry** | `N035` (effects *and* costs obligatory, since 2026-08-21), `N036`, `N037` |
| B10 | `traverse` yields no value and has no `break`; `by consuming` drains the whole queue | **open** (language/emitter) | checker accepts, `gabbro emit` refuses `[C001]` at the queue traverse (§8); retired `pruefe-notation` lists B10 as its one `ABSENKUNGSLUECKEN` entry |
| B11 | `forever` has no exit | **corrected 2026-08-20/28** | `leave <mark>` / `next` exist (`beispiele/04`, `39`, `150`); what is still missing is an exit that *carries a reason* |
| B12 | no numeric-range domain; `slots of` ambiguity | **decided 2026-08-20** | `elems of` binds an INDEX, `slots of` a slot; `lenof` outside a `format` since 2026-08-25; a range domain stays absent |
| B13 | no aggregation in `pred`; no cross-table domain | **closed** (grammar) | `count x in <domain> : pred` (`beispiele/71`); the cross-table half never carried (a foreign table name is a place). The bookkeeping *invariant* itself stays the human's L obligation |
| B14 | `option` only as a slot type; `let … else` only on a call | **closed** | `option in typeexpr` and `let … else` on a place (retired `pruefe-notation` B14a, B14b) |
| B15 | no type application (`Outcome(T,E)`, `Queue(T,N)`) | **open by decision** | no generic types; records stay monomorphic, no general `option T` (`SYNTAX.md` «SG-26»). Measured demand for generic traversal bodies: 0 duplicated bodies (retired `zaehle-traversierungen`, retired `KENNZAHLEN` register) |
| B16 | `table` knows one `slot` word and no parameters | not re-probed | — |
| B17 | `transition` writes exactly ONE place | **corrected 2026-08-28** | `transset = placeshift { "," placeshift }` exists and is used in `beispiele/02-geraet.gab` (the multi-place `transition irq_umlenken`); what really lacked was that `breaking <name> { … }` never resolved its name — now it does |
| B18 | `device` knows no phases; one class per register | **built 2026-08-28** | `class rw in setup, r in live`, rule `R009` |
| B19 | `publishes` sits on the atomic, not on the device register | **moved to the axiom layer** | K100.2 |
| B20 | `wrapping` only on slots, not on registers | **closed** (as «B32») | `reg … wrapping` (`beispiele/12`, `37`) |
| B21 | no atomic read-modify-write (high-water mark) | **closed** | `accumulates hoch : u64 merge max;` |
| B22 | strings single-line; multi-line `claim` | **closed 2026-08-17** | adjacent string literals join into one `claim` text |
| B23 | one class per register cannot express a mixed register (VT-d `FSTS`) | **built 2026-08-20** | a field may carry its own `class`; a field without one inherits the register's |
| B24 | bit positions beyond 64 / endian interplay | **decided 2026-08-18** | a position lies inside the field's own word; beyond it there is nothing to mean, so the notation is refused |
| B25 | `intty in range` is an interval, not a value set | **closed** | retired `pruefe-notation` |
| B26 | `requires` of a register has no named exit; no pre-state of a `transition` | **built 2026-08-28** | `requires … else <reason>` (`R010`/`R011`); the generator reads the pre-state through `mirrors` and measures it |
| B27 | `prim fn` has no `abi` | **retracted — a false entry** | an `asm` body with `in`/`out`/`clobbers` has existed since 2026-08-20 |
| B28 | no placeholder binder in `match` arms | not re-probed | — |
| B29 | relational precondition (`refcount -= 1`) | **decided** | `narrow … else` is the answer; the measurand `N_ritus` was built on it (§8) |
| B30 | `touches` takes an unbraced list, `effects` a braced one | **open (a wart)** | grammar unchanged: `"touches" efflist` |
| B31 | `old(place)` not usable in an expression | **corrected 2026-08-28** | `old(…)` in expressions (`beispiele/05`, `35`, `104`) |
| B32 | virtio ring counter wraps by design | **built** | `wrapping` at the register declaration |
| B33 | V-rules do not narrow a register location | **decided 2026-08-17** | deliberately: a register access is `volatile`, and `volatile` *is* the statement that the place can change between reads |
| B34 | `revoke` bound | **premise fell** | no construct needed |
| B35 | `Some`/`None` | **built** | — |
| B37 | linearity enforces *exactly once*, not *in this order* | **closed 2026-08-17** | `order { … }` with `advances a -> b` (`beispiele/22-bootstrecke.gab`) |
| B38 | `Stale(T)` that enforces revalidation is too strict | **candidate refuted; condition kept** | a value across a lock boundary re-checks *or* names a carrier; `masks IRQ` counts only under `nested masked`. Booked in the axiom layer, K100.2 |
| B39 | the MMU writes `A`/`D` itself: a writer no `effects` line names | **moved to the axiom layer** | `assume … falsifier …`; the candidate word `hardware A, D;` on `walk` was never built (it would burden the convergence bet) |
| B40 | the DTB parser checks 145 lines without error, with no tool | **a finding against the thesis, kept** | `format` buys brevity there, not safety; assumptions may name their machine (`assume <name> arch x86_64 "…"`) |
| B41 | three domains missing (B3 count): `ancestors of`, union-find, chain over an edge function | **built in part** | `ancestors of` and `descendants of`, the edge named once at the table («B41b»); union-find and the edge-function chain were not built |

**How the statuses were measured.** The retired `pruefe-notation` ran the smallest program
for each notation gap and asked the checker (8 notation gaps, plus the one emitter gap B10);
the retired `pruefe-syntax` held the examples against `SYNTAX.md`; the retired `zaehle-pflichten`
printed what still hung per fragment (all retired 2026-10-17, see git history; the statuses below are
booked results, and `gabbro pruefe` on a snippet re-measures any single one).

## 3. How the ten fragments stand today

Measured 2026-10-17 with the debug binary built that day, over the completed copies
`messung/fragmente/F01.gab` … `F10.gab` (`gabbro pruefe`), and read from the `lauf "fragmentN"`
lines of the retired `pruefe-emission` (a *Durchstich* is: emit, compile, **run**, compare
with a hand-written expected value, plus a poison edit of the C that must change the answer).

| Fragment | Area | `gabbro pruefe` on the completed copy | Durchstich (expected output) |
|---|---|---|---|
| F1 | cap space | 41 items, 0 errors, 1 hint | yes — `1 1 0 0 0 1 0 0 1 1 0 65536 4096 0 1` |
| F2 | VT-d `device` | 10 items, 0 errors, 0 hints | yes — `4096 153 7 3 256 1 6 2 1 1 0 9` |
| F3 | IPC fastpath | 27 items, **24 errors**, 2 hints | **no** — frozen on purpose (§8) |
| F4 | virtio ring | 15 items, 0 errors, 0 hints | yes — `42 1 7 99` |
| F5 | `virtio-blk` service | 32 items, 0 errors, 0 hints | yes — `qp12qBpSp 1 0 3 2 2 1 1 4711 31 512 77 0` |
| F6 | stack high-water mark | 36 items, 0 errors, 0 hints | yes — `0 0 4096 4096 1 0 1 1 0 1 0 0 0 0 1 0 1 0` |
| F7 | boot path (`order`) | 11 items, 0 errors, 0 hints | yes — `123456` |
| F8 | scheduler, `Stale(T)` | 10 items, 0 errors, 1 hint | yes — `1 1 1 0 0 1 1 1` |
| F9 | MMU page tables | 9 items, 0 errors, 0 hints | yes — `1 2236416 0 1 0 0` |
| F10 | DTB parser | 9 items, 0 errors, 0 hints | yes — `1 0 0 0 0 65` |

Nine of ten check clean and nine of ten are pierced (`F3` is the exception in both columns).
The retired `zaehle-fragmente` printed the three figures `N von 10 prüfen
sauber`, `N von 10 senken ab` and the list of pierced fragments, and the retired `zaehle-pflichten
--haengend` read the piercing ledger (not guarded today; `gabbro pruefe` over each `F0N.gab` re-measures the first).

**The frozen excerpts in this file are not the clean ones, and that is by design.**
`gabbro fragmente dokumente/FRAGMENTE.md` reports today *6 of 13 translation units with no
errors (46 %)* over this file (the F-blocks, the floating-point block and the K2 blocks) and
two `excerpt` blocks that start mid-form. The old header sentence "10 of 10 without error —
that is gate P2" is no longer true of this file; gate P2 was reached on 2026-08-15 over the
completed copies and the corpus of units, and the frozen text is only held to *named* refusals
(`korpus.rs`).

## 4. What was and was not written out

The 2026-08-14 scratchpad held six areas. The scheduler (F8), the MMU (F9), the loader (F7)
and the DTB parser (F10) were written on 2026-08-16 to decide four open classes; each of
the four demanded **no new construct** and left a finding instead («B37»–«B40»). Still not
written as fragments: a GPT/FAT parser (its `format` blocks need a *run-time* array length
where `array` requires a constant), and the checkpoint (Z4).

---

# F1 — Cap space: `delete_leaf`, `unlink`, `revoke`

**Origin (Rust):** `crates/caprock-cap/src/space.rs` — `delete_leaf`, `unlink`, `release_slot`,
`revoke`; `object.rs` (`ObjectKind`). **Caught up to the grammar of the day:** `module x { … }`
with braces, one `use` per name, `Held(CAPS)`, `costs … ops`, wrapping on the slot, the object
table as its own `table CapObjects`, `tagged type`.

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

// «B15» `variants` (SYNTAX.md:147) nimmt je Variante GENAU EINEN typeexpr. Wo Rust eine
// Felderliste inline schreibt, braucht Gabbro einen benannten Verbund. Fuenf davon.
type SchedParams = { budget : u32, period : u32, };
type ReplyRef    = { ep : EpId, caller : ThreadId, };
type MmioRange   = { phys : Pa, len : ByteLen, };
type DmaRef      = { phys : Pa, len : ByteLen, dir : DmaDir, coherence : DmaCoherence, };
type HandlerRef  = { ep : EpId, pd : PdId, sidecar : Pa, len : ByteLen, };

tagged type ObjectKind = { Memory(Region), Endpoint(EpId), Notification(EpId),
                           Tcb(ThreadId), SchedContext(SchedParams), Reply(ReplyRef),
                           PdControl(PdId), Loader(u32), Mmio(MmioRange), Irq(u32),
                           Dma(DmaRef), SyscallHandler(HandlerRef), FaultHandler(HandlerRef) };

// «B2» `lockdecl` (SYNTAX.md:471) ist von `program` aus NICHT ERREICHBAR: `item` (:111-112)
// fuehrt es nicht auf. Dieselben zwei Zeilen stehen als Beispiel in §11 der Datei, die sie
// ausschliesst. Betroffen: jede Sperre in allen sechs Fragmenten.
lock CAPS protects { plaetze, cdt } rank 0 masks irqs;
lock MEM  protects { freelist }   rank 9;

// «B16» Zwei Tabellen, weil `table` genau EIN `slot`-Wort kennt (:385-386). Der Cap-Space hat
// Slots UND Objekte; `index into CapObjects` traegt die Verbindung, aber keine Invariante
// kann sie noch aussprechen, s. B13 weiter unten.
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

    // «B16» Das `pred` einer `invariant` braucht ein `place` fuer die Tabelle
    // (`slots of place`, :239) — die Grammatik bindet aber im `table`-Rumpf keinen Namen.
    // `Self` ist hier GERATEN; §2 fuehrt `Self` nur als eingebautes Wort ohne Bindungsregel.
    invariant wurzel_ohne_vorgaenger cost O(n) runs offline :
        forall s in slots of Self :
            Self.slots[s].parent == None => Self.slots[s].prev_sibling == None;

    // «B14» Die beiden Gegenseitigkeits-Invarianten brauchen die AUFLOESUNG eines
    // `option index into` im Praedikat (`slots[s.next_sibling].prev_sibling == s`).
    // `match` loest das in einer Anweisung auf, im Praedikat gibt es dafuer nichts.
    // «B13» `refcount_matches` braucht eine Zaehlung ueber eine ZWEITE Tabelle
    // (`o.refcount == count(s in slots: s.object == o)`). `pred` (:230-247) kennt keine
    // Aggregation und keine tabellenuebergreifende Domaene. Der Kern der Buchfuehrung des
    // Faehigkeitssystems ist damit nicht formulierbar — das ist der teuerste Befund an F1.
}

// «B1» Diese Form — `spec fn … = pred;` — benutzt SYNTAX.md:287 selbst. `fndecl` (:266-274)
// laesst als Rumpf nur `block | ";"`. Ueber einen `block` ist ein Quantor NICHT erreichbar:
// `return` nimmt `expr`, und `pred` haengt nirgends unter `expr`. Ohne diese Produktion ist
// in allen sechs Fragmenten keine einzige `spec fn` schreibbar.
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
    // «B31» Die zweite Zeile ist NICHT ABLEITBAR, und zwar keine Fassung von ihr. `oldexpr`
    // haengt unter `atompred` (:235-236), nicht unter `primary` (:200): `old(x)` kann als
    // Praedikat FUER SICH stehen, aber nirgends in einem Ausdruck vorkommen — also auch
    // nicht links oder rechts von `==`. Damit ist keine Differenzaussage schreibbar, und
    // SYNTAX.md:292 gibt selbst eine an. Das trifft jede Nachbedingung, die „nachher gegen
    // vorher" sagt — die haeufigste Form, die es gibt.
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

    // «B29» -- UND SO SIEHT DIE AUFLOESUNG AUS (nachgezogen 2026-08-15).
    //
    // Die Vorlage schrieb `refcount -= 1;` und prueefte DANACH auf Null. M1 verlangt den
    // Nachweis VOR der Rechnung, und die Zaehlerregel (SPRACHE.md §1) sagt warum: ein
    // Bereich am Typ sagt nichts darueber, ob die RECHNUNG darin bleibt.
    //
    // Das Argument der Vorlage war: `refcount > 0` faellt aus der Buchfuehrungs-Invariante,
    // und die ist nach «B13» nicht aufschreibbar. **Beides stimmt und beides hilft hier
    // nicht** -- denn `narrow … else` verlangt keine Invariante, sondern eine PRUEFUNG. Der
    // `else`-Zweig ist der Ort, an dem die Verletzung sichtbar wird, statt still zu wrappen.
    //
    // Genau das ist der Unterschied zwischen EINEM Netz und ZWEIEN: die Invariante bleibt
    // der Grund, warum der Zweig nie genommen wird; der Typ bleibt der Grund, warum er
    // existieren muss.
    narrow o.slots[obj].refcount to 1 .. 80255 else {
        return Fehler::Buchfuehrung;
    }
    o.slots[obj].refcount -= 1;

    if o.slots[obj].refcount == 0 {
        // «B28» Kein Platzhalterbinder: zehn Varianten ohne Nutzlastgebrauch brauchen zehn
        // tote Namen. `_ =>` ist mit Absicht verboten, `_` als BINDER ist nicht vorgesehen.
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
    // **«B34» -- DER GROESSTE EINZELBEFUND DIESES FRAGMENTS, und er kam vom Kostenpass.**
    //
    // Die Vorlage sagte `<= 200 ops` zu. Sobald `CapSpace` seine Slotzahl nennt (`count
    // NSLOTS`, nachgetragen 2026-08-15) und die Domaenenschranke damit steht, rechnet der
    // Pass nach: **16 452 480 ops.** Fuenf Groessenordnungen.
    //
    // Die 200 waren kein Tippfehler, sondern der TYPISCHE Fall -- ein `revoke` mit wenigen
    // Nachfahren. `costs` ist aber eine SCHRANKE, und die Schranke eines `revoke` ueber
    // einer 80 256-Slot-Tabelle ist die Tabelle. **Genau diese Verwechslung -- typischer
    // Fall statt oberer Schranke -- ist der Grund, warum die Zahl nachgerechnet und nicht
    // geglaubt wird**, und sie ist hier zum zweiten Mal aufgeschlagen (zuerst bei A4:
    // 4 096 zugesagt, 831 488 gerechnet).
    //
    // **BERICHTIGT 2026-08-15.** Hier stand: „Caprock begrenzt `revoke` ueber die
    // CDT-Tiefe, und diese Schranke ist in Gabbro nicht ausdrueckbar." **Das war aus dem
    // Gedaechtnis geschrieben und ist falsch.** `cdt_step_limit()` liefert
    // `self.slots.len()` (`caprock-cap/src/space.rs:932-933`) -- **dieselbe Schranke, die
    // Gabbro rechnet.**
    //
    // Und der Kernel nimmt sie ZWEIMAL, innen und aussen (`:635`, `:648`); seine eigene
    // obere Schranke ist `slots.len()^2`, also rund 390-mal groesser als diese Zahl.
    // **Gabbros Schranke ist die schaerfere.** Es fehlt kein Konstrukt -- die 200 waren
    // schlicht der typische Fall statt der Schranke, und genau dagegen ist der Kostenpass
    // gebaut (`memos/M-kostenmass.md`).
    costs     <= 16452480 ops
{
    // «B10» `traverse` liefert KEINEN Wert (:337-341) und es gibt kein `break`. Der
    // Hoechststand `peak_revoke_ops` — im Rust-Original der Beleg dafuer, dass die Schranke
    // nie gegriffen hat — ist damit nicht erhebbar. Die SCHRANKE faellt durch `by consuming`
    // weg, die MESSUNG der Schranke ebenfalls, und nur die erste war beabsichtigt.
    traverse victim over descendants of c.slots[s] by consuming
        touches consumes c.slots, writes o.slots, writes rf
    {
        delete_leaf(c, o, a, rf, victim);
    }
}

// Nachgetragen 2026-08-15: drei Gerufene wurden benutzt und nie erklaert. Ohne `costs` am
// Gerufenen kann der Kostenpass die Zusage des Rufers nicht nachrechnen -- und er SAGT das
// (`K003`), statt stillschweigend zu schaetzen. Genau dafuer ist die Absage da.
extern fn free_region(a : ptr<normal, rw> Allok, m : MemObj) effects { writes a } costs <= 32 ops;
extern fn push_dma(rf : ptr<normal, rw> Finalized, d : DmaObj) effects { writes rf } costs <= 8 ops;
extern fn push_reply(rf : ptr<normal, rw> Finalized, r : ReplyObj) effects { writes rf } costs <= 8 ops;


}
```

**Verdict at the freeze: fits with findings** — B1, B2, B10, B13, B14, B15, B16, B28, B29, B31.

The body carries. `unlink` stands line for line; `delete_leaf` loses the catch-all branch over
ten `ObjectKind` variants (Caprock has added *five* since the Rust was written — each would
silently have fallen into `_ => {}`); `revoke` shrinks from 26 body lines to 4, because
`by consuming` carries termination and leafness. What did not carry is the bookkeeping itself:
`refcount_matches` was unformulable (B13), and `refcount -= 1` hung on exactly that (B29).

**The proof part is not a finding, it is the line drawn.** A hand-written second half
(`ghost let`, `assert … by { … }`, `lemma … { induction over the slot table }`) would be needed
for the preservation of `kind_zeigt_zurueck` by `unlink`, which splits into four cases;
`SYNTAX.md` lists hand-written lemmata among what does not exist, and states the price — no
emergency exit. Either the property falls out of the construction or it falls out of the
language.

**Today:** the completed copy `F01.gab` checks (0 errors) and is pierced. One real defect
stays booked as `TODO.md` **O4**: `cdt_wohlgeformt` quantifies over `slots of c` — the whole
table, not the used slots — so one free slot falsifies it, and `unlink`'s
`ensures c.slots[s].parent == None` contradicts its own `maintains` four lines away. A solver
found it; no Gabbro pass sees it, and the Durchstich does not either (it measures what the C
computes, not what the promise claims).

---

# F2 — VT-d: the remapping unit as a `device`

**Origin:** `crates/caprock-hal/src/x86_64/vtd.rs` (register locations, `GCMD_STATE_MASK` —
trap 4 literally —, `frr_off`, `read_frr`, the state bits on the command write). Here the new
grammar helped most: four of the draft's seven gaps closed (multi-bit fields `@[hi:lo]`,
`bank … at CAP.FRO * 16 …` for run-time register locations, `mirrors GCMD from GSTS;`).

```gabbro
device Vtd(base : Pa) at mmio {
    // Falle 4, x86-Fassung: GCMD ist KEIN Read-Modify-Write. Genau eine Zeile, einmal je
    // Geraet. Sie ersetzt `GCMD_STATE_MASK` samt der Kommentarwand in vtd.rs:42-52.
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

    // «B23» FSTS ist GEMISCHT: 7:0 sind RW1C, 15:8 (FRI, der Index des ersten besetzten
    // Fault-Registers) sind r. `regdecl` (:430) traegt EINE Klassenangabe je Register.
    // `class w1c` macht das Lesen von FRI untypisierbar — und FRI ist die Groesse, mit der
    // der Treiber die Aufzeichnung ueberhaupt findet (vtd.rs:503).
    reg FSTS : u32 @0x034 class w1c
        fields { PFO @0, PPF @1, AFO @2, APF @3, IQE @4, ICE @5, ITE @6, PRO @7, FRI @[15:8], }

    reg IQH  : u64 @0x080 class r
    reg IQT  : u64 @0x088 class rw
    reg IQA  : u64 @0x090 class rw  fields { DW @11, }
    reg ICS  : u32 @0x09c class w1c fields { IWC @0, }
    reg IRTA : u64 @0x0b8 class rw  fields { EIME @11, }

    // Geschlossen: Registerlage aus einem GELESENEN Feld. Der Index ist ueber `count`
    // M1-beschraenkt; `frr_off` (vtd.rs:442) rechnet dieselbe Adresse von Hand aus.
    bank FRR at CAP.FRO * 16 stride 16 count 256 {
        reg FR_LO : u64 @0x0 class r
        // «B24» Das F-Bit ist Bit 63 des OBEREN Wortes, `grund` liegt in 39:32 desselben.
        // `bitpos` (:146) sagt nichts darueber, worauf sich eine Bitlage jenseits von 64
        // bezieht und wie sie mit `endian` zusammenwirkt. Hier bezogen auf FR_HI.
        reg FR_HI : u64 @0x8 class w1c
            fields { SID @[15:0], TYPE @[29:28], GRUND @[39:32], AT @[61:60], F @63, }
    }
    bank IOTLB at ECAP.IRO * 16 stride 16 count 1 {
        reg IVA : u64 @0x0 class w
        reg CMD : u64 @0x8 class rw
            fields { DID @[47:32], DR @49, DW @50, IAIG @[58:57], IIRG @[60:59], IVT @63, }
    }

    // «B26» Der Vorzustand steht an einem NICHT LESBAREN Ort. `mirrors` sagt, WOHER die
    // mitgefuehrten Bits kommen; ob es damit auch den Vorzustand einer `transition` an
    // `GCMD.TE` aus `GSTS.TES` bezieht, sagt SYNTAX.md (:428, :434) nicht. Die Vorlage hat
    // diesen Widerspruch als unaufloesbar gefuehrt; er ist jetzt halb aufgeloest.
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

// «B25» `grund` soll genau die zwoelf Werte von FaultGrund tragen. `intty` traegt ein
// INTERVALL (:139), keine Wertemenge. Hier geht es nur, weil 0x01..0x0c zufaellig
// zusammenhaengend ist; bei einem geloecherten Code waere das Feld nicht bindbar.
// «B24» Zweitens: der Satz besteht aus zwei 64-Bit-Woertern -- **und seit dem 2026-08-18
// steht das im Traegertyp statt im Kommentar.** Der urspruengliche Text las: *„Die Bitlagen
// unten sind auf das jeweilige Wort bezogen, weil `format` keine Wortbreite kennt."* Sie
// kennt sie: die Wortbreite IST der Feldtyp, und eine Lage jenseits davon bedeutet nichts.
//
// **Nachgezogen am 2026-08-19, als `N007` in den Pruefer kam.** Sieben Stellen fielen, und
// eine davon war ein Widerspruch INNERHALB dieser Datei: `typ` stand hier als `@[13:12]`,
// das Register `FR_HI` derselben Einheit fuehrt `TYPE @[29:28]`. *Die zweite Zahl ist die
// gemessene; die erste haette mit `sid @[15:0]` ueberlappt.*
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
// «B22-nah, eigener Fall» `where f_bit == 1` WEIST ein leeres Register AB, statt „leer" zu
// MELDEN. Das ist der Unterschied zwischen Absage und Abwesenheit, und `format` kennt nur
// die Absage. Im Rust-Original ist genau das der Unterschied zwischen „kein Fault" und
// „Aufzeichnung nicht lesbar" (vtd.rs:451).

format Slpte @version 1 endian little {
    R    : u64 @0,
    W    : u64 @1,
    SNP  : u64 @11,
    ADDR : u64 @[63:12],
}

// «B24» Der Kontexteintrag ist 128 Bit breit, und **die Entscheidung verweigert `@[66:64]`
// ausdruecklich**: eine Lage liegt im eigenen Wort, `u64` hat die Bits 0 bis 63, also nennt
// `@[66:64]` nichts. *Der Ausweg steht in derselben Zeile von `PFLICHTEN.txt`:* zwei Woerter,
// und der Schreiber nennt das zweite, statt dass der Erzeuger es raet.
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

**Verdict at the freeze: fits with findings** — B23, B24, B25, B26. The best result of the six:
`mirrors GCMD from GSTS;` is **one line** where the Rust has a constant plus eleven comment
lines plus three hand-done sites. What remained was the register-class finding (B23: `FSTS` is
`w1c` in bits 7:0 and read-only in 15:8, and one class per register made the fault-record index
unreadable) — all built since.

**Today:** the only frozen block that is clean under the checker, pinned by
`f2_das_geraetefragment_bleibt_sauber`; the completed copy is pierced (`4096 153 7 3 256 1 6 2
1 1 0 9`; five `reserved` fields were the only addition).

---

# F3 — IPC: the fastpath `Endpoint::call`

**Origin:** `crates/caprock-ipc/src/lib.rs` (`call`, `caller`; trap D11 sits in the overflow
branch of the sender queue). **Caught up:** `state X`, `Some(x) => { }`, `costs … ops`,
`over queue e.receivers`, a monomorphic `TidQueue`.

```gabbro
module caprock::ipc {

const QUEUE_CAP : u32 = 32;
const NCORES    : u32 = 64;   // nachgetragen 2026-08-15
const MSG_WORDS : u32 = 6;

reason IpcResult {
    Ok           = 0 "Rendezvous vollzogen"
    ErrBadCap    = 2 "Endpoint nicht belegt"
    ErrQuiescing = 8 "Endpoint stillgelegt, keine neue Transaktion"
    ErrEpFull    = 9 "Warteschlange voll, D11: benannt statt still"
    exhaustive
}

// «B15» Monomorph ausgeschrieben. `Queue(T, const N)` ist nicht schreibbar: `typeexpr`
// (:137) hat keine Anwendungsform, und `params` (:150) nimmt Werte, keine Typen.
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

// «B17» HIER BRICHT DAS FRAGMENT. `transition` (:434) schreibt GENAU EIN `place`:
//     transition = "transition" ident "{" place ":" expr "->" expr "}" …
// Die ganze Aussage des Fragments ist aber, dass `caller` und `reply_owner` NIE HALB
// gesetzt werden — zwei Orte in EINEM Zug. In Caprock steht das als Kommentar
// ("stets gemeinsam gesetzt/geloescht"); Gabbro sollte es zur Ableitung machen und kann es
// nicht. Zweitens nennt `state` (:414) den Typ nicht, ueber dem es steht.
// Drittens bindet `Some(cl)` im Zielausdruck einen frischen Namen — dafuer gibt es keine
// Produktion. Die drei Zeilen unten sind AUSKOMMENTIERT, weil sie nicht schreibbar sind:
//     state Rendezvous over Endpoint {
//         transition open  { caller : None -> Some(cl), reply_owner : None -> Some(sv) }
//         transition close { caller : Some(c) -> None,  reply_owner : Some(s) -> None }
//     }

// «B12» `forall i in 0 ..< MSG_WORDS` ist nicht schreibbar: die sieben Domaenen (:238-244)
// enthalten keinen Zahlenbereich. Ersatz ueber `elems of` — und damit steht die zweite
// Frage im Raum: bindet `elems of` ein ELEMENT und `slots of` einen INDEX? SYNTAX.md
// benutzt beide Lesarten und legt keine fest.
spec fn msg_kopiert(dst : ptr<normal, r> Frame, src : ptr<normal, r> Frame) -> bool
    effects { pure }
    = forall i in elems of dst.msg : dst.msg[i] == old(src.msg[i]);

// «B9» Der Ersatz fuer `&mut dyn SchedOps`: `fnptr` (:148) traegt KEINEN Vertrag —
// kein `requires`, kein `ensures`, kein `effects`. Genau dafuer war der Verbund gedacht
// ("der Vertrag des Rueckrufs muss am Zeigertyp stehen"). Er traegt nur noch die Signatur.
// «B8» Und gerufen werden kann durch ihn ueberhaupt nicht: `call = path "(" … ")"` (:202);
// `ops.current_id(core)` ist kein `call`, weil `ops.current_id` ein `place` ist.
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
    // «B6» Die Nachbedingungen des Originals sprechen ueber `result`. `fndecl` (:266-274)
    // bindet fuer den Rueckgabewert KEINEN Namen; `old(place)` gibt es, ein `result` nicht.
    requires  Held(EPS), e.slots[core].used
    maintains antwortpflicht_paarig
    // `reads dienste` steht hier, weil `current_id`/`frame_of` es nennen: seit 2026-08-15
    // schliesst eine Wirkungsliste die der Gerufenen ein (`E008`). **Die Zeile war vorher
    // unvollstaendig, und kein Werkzeug konnte es sagen** -- genau der Posten, der `effects`
    // erst kompositional macht.
    effects   { writes e.slots, locks SCHEDS, writes frames, consumes e.slots,
                reads dienste }
    costs     <= 2000 ops
{
    if e.slots[core].quiescing {
        set_reg(f, SYSNO_RESULT, IpcResult::ErrQuiescing);
        return f;
    }
    let caller = current_id(dienste, core);

    // «B10» Der Fastpath sucht den ERSTEN lebenden Empfaenger und hoert dann auf. `traverse`
    // liefert keinen Wert und kennt kein `break` — mit `by consuming` wird deshalb die
    // GANZE Warteschlange geleert, auch die Empfaenger hinter dem gefundenen. Das ist keine
    // Wortreichheit, sondern ein anderes Programm: aus einem Rendezvous wird ein Aderlass.
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
            // D11 woertlich: der Ueberlaeufer wird NICHT blockiert, sondern benannt
            // abgewiesen. Das traegt die Grammatik, und es ist der beste Zug in F3.
            set_reg(f, SYSNO_RESULT, IpcResult::ErrEpFull);
            return f;
        }
        return block_current(dienste, core, f);
    }

    transfer(f, frame_of(dienste, picked));
    set_reg(frame_of(dienste, picked), SYSNO_RESULT, IpcResult::Ok);
    set_reg(frame_of(dienste, picked), EP_BADGE, 0);
    // «B17» hier stuende `open(e, caller, picked);` — der Uebergang, der beide Orte in
    // EINEM Zug schreibt. Ohne ihn zwei Zuweisungen, und die Invariante gilt dazwischen nicht.
    e.slots[core].caller      = Some(caller);
    e.slots[core].reply_owner = Some(picked);
    if owner_core(picked) == core {
        return switch_to(dienste, core, f, picked);
    }
    unblock(dienste, picked);
    return block_current(dienste, core, f);
}


// Nachgetragen 2026-08-15: `set_reg` wurde zweimal gerufen und nie erklaert.
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

**Verdict at the freeze: does NOT fit** — B17 lethal (a `transition` wrote exactly one place),
plus B6, B8, B9, B10, B12, B15. The fragment existed to show that Caprock's comment *"`caller`
and `reply_owner` are always set and cleared together"* becomes a derivation instead of a
promise. B17 has since been corrected (§2); B10 (`traverse` cannot return the *first* hit
without emptying the queue — a different program) is still open.

**Three promises of the draft were deliberately not taken over**, and the reason is not
grammar: `ensures e.caller is Some(cl) => cl == current_id(ops, core)` is **false** (a second
caller lands in the `None` branch while `caller` stays the first); `msg_copied` is declared,
counted into its own metric and gates **no** `ensures` — the only functional property of a
fastpath, *the message arrived*, gates nothing; `locks SCHEDS` without an index hides that the
cross-core branch takes a foreign core's lock. **The lesson belongs to the bookkeeping:** a
metric formed out of unchecked promises rewards the false promise, because it is short.

**Today — the one fragment that is still not pierced**, and the reason is *decided*, not
neglected (§8): 24 errors (the 18 of 2026-09-04 plus 6 `N574`, the refusal of 2026-09-30 that a
foreign body takes no function pointer, hit by the scheduler vtable `SchedOps` handed to
`extern fn block_current`/`switch_to`/…), classified **0 plumbing / 9 rule decisions / 9 the
program is wrong**. A rewritten, runnable fast path exists
(`messung/proben/probe-ipc-fastpath-durchgestochen.gab`, run name `ipcfastpath`) and was *not*
accepted as F3's Durchstich, because it replaced the load-bearing statement.

---

# F4 — The driver: virtio transport, ring, buffer ownership

**Origin:** `crates/caprock-virtio/src/lib.rs` (register locations, `publish`, `poll_used`,
`QUEUE_SIZE` as a foreign number, the status word assembled by hand), `owned.rs` (buffer
ownership).

```gabbro
device VirtioPci(base : Pa) at mmio {
    reg DEVICE_FEATURE_SEL : u32 @0x00 class w
    reg DEVICE_FEATURE     : u32 @0x04 class r
    reg DRIVER_FEATURE_SEL : u32 @0x08 class w
    reg DRIVER_FEATURE     : u32 @0x0c class w
    reg DEVICE_STATUS      : u8  @0x14 class rw
        fields { ACK @0, DRIVER @1, DRIVER_OK @2, FEATURES_OK @3, }
    reg QUEUE_SELECT       : u16 @0x16 class w
    // «B26» `QUEUE_SIZE` ist eine FREMDE Zahl (lib.rs:494). `regdecl` traegt ein
    // `requires`, aber keinen benannten Ausgang: aus „zu gross" wird kein `reason`-Wert.
    // Die Vorlage schrieb `else QueueTooBig`; das gibt es nicht.
    reg QUEUE_SIZE         : u16 @0x18 class rw requires QUEUE_SIZE <= QMAX
    reg QUEUE_ENABLE       : u16 @0x1c class w
    reg QUEUE_NOTIFY_OFF   : u16 @0x1e class r
    reg QUEUE_DESC         : u64 @0x20 class w
    reg QUEUE_DRIVER       : u64 @0x28 class w
    reg QUEUE_DEVICE       : u64 @0x30 class w

    // Das traegt, und es ist der Gewinn dieses Fragments: `transition` nennt das GANZE
    // geschriebene Wort. lib.rs:533 setzt es an vier Stellen von Hand zusammen.
    transition ack    { DEVICE_STATUS: 0 -> ACK } effects { writes DEVICE_STATUS }
    transition drv    { DEVICE_STATUS: ACK -> ACK | DRIVER } effects { writes DEVICE_STATUS }
    transition featok { DEVICE_STATUS: ACK | DRIVER -> ACK | DRIVER | FEATURES_OK }
        effects { writes DEVICE_STATUS }
    transition drvok  { DEVICE_STATUS: ACK | DRIVER | FEATURES_OK
                                    -> ACK | DRIVER | FEATURES_OK | DRIVER_OK }
        effects { writes DEVICE_STATUS }
    // «B26» `transition reset { DEVICE_STATUS: any -> 0 }` ist nicht schreibbar: es gibt
    // keinen Platzhalter fuer den Vorzustand. Ein Reset gilt aus JEDEM Zustand — genau die
    // Aussage, die eine Uebergangstabelle braucht, damit sie vollstaendig ist.
}

// «B18» HIER BRICHT DIE HAELFTE VON F4. Die Vorlage schrieb den Ring als `device` mit
// Phasen und einer Registerklasse JE PHASE:
//     phases { Setup, Live }
//     reg USED_IDX : u16 wrapping @0x202 class rw in Setup, r in Live
// `device` (:426-435) kennt keine Phasen, und `regdecl` (:430) traegt eine Klasse.
// Damit ist „`used` gehoert dem Geraet" wieder ein Kommentar. Dieselbe Stelle traegt eine
// BEZAHLTE Falle: bei einer wiederverwendeten Region steht im `used`-Ring der Endstand der
// vorigen Treiberfassung, und die Vorlage machte daraus die `requires`-Klausel von `enable`.
// «B20» Dazu: `wrapping` gehoert an `slottype` (:388), nicht an `intty` (:139). Der
// avail-Index ist ein REGISTER und laeuft laut virtio-Spezifikation bei 65536 um; als
// `u16 in 0 ..< n` waere er falsch, als `u16 wrapping` nicht schreibbar.
// «B19» Und die Barrieren: `AVAIL_IDX … publishes { DESC, AVAIL_RING } release` ist die
// Form, aus der der Uebersetzer die fuenf `fence()`-Aufrufe des echten Treibers ableiten
// sollte. `publishes` sitzt an `atomicdecl` (:468) — das nach «B2» nicht einmal erreichbar
// ist — und nicht an einem Geraeteregister. SYNTAX.md fuehrt genau das als offenen Punkt
// (:598): die sicherheitskritischste Veroeffentlichung im Baum ist gar kein Atomic.

// **`N049`, 2026-09-01: dieser Block war in sich WIDERSPRUECHLICH, und die Regel hat es im
// ersten Lauf gefunden.** Er fuehrte dreimal `count 256`, waehrend seine Versaetze die einer
// Warteschlange der Groesse **16** sind. Bei 256 deckt `DESC` allein `0x000..0x1000` -- und
// damit liegt **jedes andere Register und jede andere Bank dieses Geraets INNERHALB von
// `DESC`**. `DESC[16].addr` und `AVAIL_FLAGS` waeren dieselben Bytes.
//
// Bei 16 geht die Rechnung genau auf, und es ist die klassische geteilte virtio-Schlange:
// `DESC` 16x16 = `0x100`, `avail` bei `0x100` mit Ring `0x104..0x124`, `used` bei `0x200`
// mit Ring `0x204..0x284`. *Die Versaetze waren richtig; die Anzahl war es nicht.*
device Virtq(base : Iova, n : u16 in 1 .. QMAX) at dma {
    bank DESC at 0x000 stride 16 count 16 {
        reg addr  : u64 @0x0 class w
        reg len   : u32 @0x8 class w
        reg flags : u16 @0xc class w fields { NEXT @0, WRITE @1, }
        reg naechst : u16 @0xe class w
    }
    reg AVAIL_FLAGS : u16 @0x100 class rw
    reg AVAIL_IDX   : u16 wrapping @0x102 class rw
    bank AVAIL_RING at 0x104 stride 2 count 16 { reg e : u16 @0x0 class w }
    reg USED_FLAGS  : u16 @0x200 class rw
    reg USED_IDX    : u16 @0x202 class rw
    bank USED_RING at 0x204 stride 8 count 16 {
        reg id  : u32 @0x0 class rw
        reg len : u32 @0x4 class rw
    }
}

// Der Ersatz fuer die Phasen ohne neuen Mechanismus: die Phase ist ein linearer
// Geisterwert, woertlich `BootPhase` eine Ebene tiefer. Nach `queue_arm` gibt es keinen Weg
// mehr, `USED_IDX` zu schreiben — nicht weil ein Waechter es verbietet, sondern weil die
// Marke verbraucht ist.
// «B3» `linear ghost type QueueSetup(Virtq);` schreibt eine TYPliste in die Klammern.
// `typedecl` (:135-136) verlangt dort `params`, also `ident ":" typeexpr`. SYNTAX.md
// macht denselben Fehler in seinen eigenen vier Beispielen (:162-167), `Held(Lock)`
// eingeschlossen — und `Held` steht in jedem `requires` dieser Datei.
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
    // Nachgezogen 2026-08-15: die Vorlage sagte `<= 4 ops` zu, der Rumpf kostet 9. Die Zahl
    // ist mit `gabbro kosten` abgelesen, nicht geschaetzt (WERKZEUGKASTEN.md W2).
    // **Nachgezogen 2026-09-13 (Lane 139, F1): der Rumpf kostet 10.** Die Schreibung zaehlt
    // ihren Zielindex `platz` (`+1`), und `+=` laedt und rechnet (`+2`).
    costs   <= 10 ops
{
    // Der Nenner schliesst die Null aus, weil `n : u16 in 1 .. QMAX` es tut (:216).
    let platz = q.AVAIL_IDX % q.n;
    q.AVAIL_RING[platz].e = head;
    // Nachgezogen 2026-08-15: der Ringzaehler LAEUFT UEBER, und zwar mit Absicht --
    // virtio zaehlt modulo 2^16 und nimmt den Rest gegen `q.n`. Die Vorlage schrieb
    // `+= 1` auf einem blanken `u16`; damit stand die Absicht nirgends, und die
    // Zaehlerregel (SPRACHE.md §1) faellt zu Recht.
    //
    // **«B32» -- UND HIER FAELLT EIN NEUER BEFUND.** Die Sprache laesst den Umlauf an der
    // DEKLARATION aussprechen, nicht an der Rechnung: `slottype = intty "wrapping"`
    // (SYNTAX.md:500). Das ist die staerkere Form -- der Umlauf gilt dann fuer jede Rechnung
    // auf dem Feld, nicht nur fuer die eine, an die jemand gedacht hat.
    //
    // **Aber `AVAIL_IDX` ist kein Slot, sondern ein REGISTER**, und `regdecl` (:545-548)
    // kennt `wrapping` nicht. Ein Hardwarezaehler, der per Entwurf umlaeuft -- der
    // haeufigste Fall ueberhaupt in einem Geraetetreiber -- kann seine Absicht nicht
    // aussprechen. Bis das geschlossen ist, steht hier die Pruefung davor; sie ist an
    // dieser Stelle NICHT die ehrliche Form, sondern der Ersatz dafuer.
    // **«B32» ist geschlossen (2026-08-15), und der Ersatz faellt weg.** Bis dahin stand
    // hier ein `narrow` mit einem `else`-Zweig, der die Absicht NICHT ausdrueckte, sondern
    // umging. Jetzt sagt die Deklaration `reg AVAIL_IDX : u16 wrapping`, was virtio meint,
    // und die Rechnung darf schlicht dastehen.
    //
    // «B33» bleibt daneben offen: die V-Regeln verengen den Typ eines REGISTERORTES nach
    // `if … == N { return; }` nicht -- nur `narrow` traegt die Tatsache. Ob das Absicht ist
    // (ein Register kann sich zwischen Pruefung und Rechnung aendern!) oder eine Luecke,
    // entscheidet der Ordner. **Wenn es Absicht ist, gehoert die Begruendung
    // aufgeschrieben** -- sie waere ein starkes Argument.
    q.AVAIL_IDX += 1;
}

impl fn poll_used(q : ptr<dma, r> Virtq, von : u16) -> u32
    effects { reads q }
{
    // Das traegt unveraendert, und die Reihenfolge stimmt mit der Produktion (:343-348):
    // bounded, progress, on_exceeded, effects. Der Ueberlauf ist BENANNT.
    retry warten until q.USED_IDX != von
        bounded     MAX_POLL ops
        progress    device_completes_or_faults
        on_exceeded DeviceSilent
        effects     { reads q }
    { }
    let s = von % q.n;
    // «B7» `return Completion { id: …, len: … };` ist nicht schreibbar: `primary` (:200)
    // kennt keinen Verbund- und keinen Feldliteral. Eine Funktion kann einen `structty`
    // also nicht HERSTELLEN. Deshalb hier ein Skalar statt des Verbunds.
    return q.USED_RING[s].id;
}
```

**Verdict at the freeze: fits with findings** — B3, B7, B18, B19, B20, B26, B30. The transport
carries completely and takes trap 4 in its virtio form with it (the status word is no longer
assembled by hand); `retry` carries the poll word for word. The ring did not: phases, a register
class per phase and `publishes` on a device register were missing — together the carriers of two
paid-for traps (the reused virtqueue, the barrier out of the address space). B18/B26/B32 are
built; B19 went to the axiom layer. **Today:** pierced (`42 1 7 99`).

---

# F5 — Userspace: the service loop of `virtio-blk`

**Origin:** `programs/hardware/virtio-blk/src/main.rs` (`run`, the loop, `OP_STOP`, the op
codes), `programs/libcaprock` (the syscall entry).

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

// «B27» Der Syscall-Einstieg: `arch ident` gibt es (:273), die REGISTERBELEGUNG nicht.
// Die Vorlage schrieb dafuer einen `abi { in rax = nr, …, trap 0x80 }`-Block; `fndecl`
// kennt ihn nicht. Damit hat der einzige Ort, an dem 168 gemessene `asm!`-Stellen
// zusammenlaufen sollten, in der Grammatik keinen Traeger — die vertrauenswuerdige Flaeche
// schrumpft nicht, sie wandert in eine `prim`-Deklaration ohne Inhalt.
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

    // «B14» `let mut capacity : option Sectors = none;` ist nicht schreibbar: `option` steht
    // nur in `slottype` (:387), nicht in `typeexpr` (:137). Der Fall „noch nie gelesen" wird
    // damit wieder eine 0 — genau die Deutung, gegen die das Fragment geschrieben war.
    let mut capacity : u32 = 0;

    // «B11» HIER BRICHT F5. `forever` (:350-354) hat KEINEN AUSGANG. Die Vorlage schrieb
    //     awaits recv(EP)   leaves ServiceExit   …   { … leave EndpointGone; }
    // und begruendete es mit D0: der echte Code hat an dieser Stelle
    // `if m.result != OK { break; }`, und dass dieser Austritt keinen Namen trug, hat zehn
    // Tage gekostet. In der Grammatik von heute gibt es weder `leave` noch `break` noch
    // `continue`; SYNTAX.md fuehrt das selbst als offenen Punkt (:603) und vermutet, es sei
    // versehentlich. Es ist der Unterschied zwischen „D0 faellt durch Konstruktion" und
    // „die Dienstschleife ist nicht schreibbar".
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
                // «B7» `reply(EP, [Ok, r, MAX_SECTORS, SECTOR]);` ist nicht schreibbar:
                // `primary` (:200) kennt kein Feldliteral. Vier Argumente statt eines Feldes.
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
                // «B11» hier stuende `leave Stopped;`. Ohne Ausgang bleibt nur `exit()` —
                // also der Sprung aus der ganzen Funktion, und die Aufraeumzusage der
                // Funktion wandert an zwei Stellen. Das ist woertlich die Klasse, die C8
                // bezahlt hat: ein neuer Abweispfad erbt die Aufraeumpflicht des alten nicht.
                exit();
            }
        }
    }
}

// Nachgetragen 2026-08-15: `exit` und `signal` wurden benutzt und nie erklaert.
// Ohne `-> never` an `exit` kann kein Pass sehen, dass die Fehlerzweige nicht
// durchfallen -- sechs `S002` kamen allein daher.
extern fn exit() -> never effects { diverges };
extern fn signal(n : u64, w : u64) effects { writes NTFN };
extern fn watchdog_schlug_an() -> never effects { diverges };

}
```

**Verdict at the freeze: does NOT fit** — B11 lethal (a service must be able to leave its loop
*by name*; `forever` had no exit), plus B7, B14, B27. What carried, carried well: `match` is
exhaustive, so the `_ => reply(ST_BADOP)` branch exists once instead of in every server; the
four `map_window` refusals are forced through `let … else`. B11 was corrected on 2026-08-20
(`leave <mark>` exists and lowers to `goto marke_ende;`), B27 was a false entry, B14 is closed.

**Completing it found three names that belong to C** (`exit`, `signal`, `recv`), and none is
visible at `cc` because the generated unit includes no POSIX header — the linker then finds the
real symbol behind whatever the unit declared: a *silent wrong binding*. They were renamed in
the completed copy (`N046`'s own advice). The same run found that `N046` ignored the error
channel (`-> T or R` rewrites the C signature) — repaired. **Today:** pierced, with a
fingerprint of the whole dispatch as expected value (`qp12qBpSp …`).

---

# F6 — Test scaffold: the stack high-water mark

**Origin:** `kernel/src/kstackmark.rs` (`unberuehrt`, `messen`, `fetch_max`/`fetch_min`,
`marke`, `urteil`, the calibration). `publishes nothing` and `relaxed` closed two of the
draft's three findings before it was even run (the ordering set had left out the most frequent
ordering, 779 of 2 257 measured accesses).

```gabbro
module kernel::kstackmark {

reason Stackart {
    El0  = 0 "der 16-KiB-EL1-Stack eines EL0-Threads"
    Kern = 1 "der 64-KiB-Stack eines Kernel-Threads"
    exhaustive
}

const STACK_MAX : u64 = 65536;   // nachgetragen 2026-08-15: benutzt, nie erklaert
type Bytes = u64 in 0 .. STACK_MAX;

// **Nachgetragen 2026-08-19, wie `STACK_MAX` am 2026-08-15: benutzt, nie erklaert.**
// Der Rumpf unten liest `s.worte`, `s.len` und rechnet `i * 8` -- ein Wort ist acht Bytes,
// also traegt ein Stack von `STACK_MAX` Bytes `STACK_MAX / 8` Worte. **Die Zahl ist
// ABGELEITET und nicht erfunden**; sie steht dreimal im Rumpf und stand nirgends.
//
// *Ohne diese Zeile hat `elems of s.worte` keine Schranke, und «H2.1» kann nicht greifen --
// nicht weil die Regel zu schwach waere, sondern weil der Ausschnitt seinen Traeger nicht
// nennt.* Der Befund gehoert zum Ausschnitt, nicht zu Gabbro.
const STACK_WORTE : u64 = 8192;
type Stack = { worte : [u64; STACK_WORTE], len : Bytes, };

const MIND_RESERVE_NENNER : u32 in 1 .. 64 = 8;
const MIND_MESSUNGEN      : u32 = 2;

// «B2» Alle zehn Zeilen unten sind `atomicdecl` (:468) — von `program` aus NICHT
// ERREICHBAR, weil `item` (:111-112) sie nicht auffuehrt. Sie stehen hier trotzdem, weil
// sie sonst nirgends stehen koennten; ein Modul, das sie enthaelt, ist heute nicht
// ableitbar. Betrifft baumweit 594 Atomic-Deklarationen.
// «B21» `accumulates max` / `accumulates min` / `accumulates +` gibt es nicht. Genau sie
// SIND die Wasserstandsmarke (`TIEFE_MAX.fetch_max`, kstackmark.rs:199-203); ohne sie ist
// die Messgroesse dieses Fragments nicht schreibbar. Baumweit 213 Lese-Aendere-Schreib-
// Zugriffe, davon 19 `fetch_max`/`fetch_min`. SYNTAX.md fuehrt den Punkt selbst (:600) und
// nennt ihn den ersten Kandidaten fuer „zwei geforderte Eigenschaften widersprechen einander".
// «B14» `frei_min : option Bytes` ist nicht schreibbar (`option` nur als `slottype`). Der
// echte Code rechnet spaeter `groesse.saturating_sub(frei_min)` und macht damit aus
// „nie gemessen" eine 0 — die Deutung, die eine Nullmessung unsichtbar macht.
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
    // **Berichtigt 2026-08-18, gefunden von `M109`.** Hier stand `unberuehrt <= s.len` --
    // der FUNKTIONSNAME an der Stelle, an der `result` hingehoert. Gabbro hat das Wort;
    // die Vorlage kam aus einer Sprache, in der der Name das Ergebnis bezeichnet.
    // *Die Zeile stand seit dem Schnitt da und ist niemandem aufgefallen, weil `ensures`
    // von keinem Pass gelesen wurde.*
    ensures  result <= s.len
    effects  { reads s }
{
    let mut i : u64 in 0 .. STACK_MAX = 0;
    // «B30» `touches` nimmt eine `efflist` OHNE Klammern (:340), waehrend `effects`
    // ueberall sonst geklammert ist. Die Vorlage schrieb `touches { reads s }`.
    traverse w of s over elems of s.worte by unvisited decreases (lenof(s.worte) - i)
        touches reads s
    {
        if w != MUSTER { return i * 8; }
        // ~~Nachgezogen 2026-08-15: die Schranke faellt zwar aus der Domaene (die
        // Traversierung laeuft ueber `s.worte`), **aber M1 sieht das nicht** -- der
        // Zaehler ist eine gewoehnliche lokale Variable. Der `else`-Zweig kann nicht
        // genommen werden und muss trotzdem dastehen.~~ *(2026-08-15)*
        //
        // **Entfallen am 2026-08-19 mit «H2.1».** M1 sieht es jetzt: ein Zaehler, der in
        // einer beschraenkten Traversierung hoechstens einmal je Durchgang waechst, erbt
        // die Schranke seiner Domaene -- an der Zuwachsstelle `i <= c + (B-1)*k`.
        // *Die Regel ist die einzige Ausnahme von `SPRACHE.md`:657 („Loops carry no facts
        // inward"), und der Unterschied zwischen Ausnahme und Loch liegt in der Richtung:
        // die Tatsache kommt nicht von aussen, sondern aus der Schleifenform selbst.*
        i += 1;
    }
    return i * 8;
}

// «B7» Das Original gibt ein PAAR zurueck (`-> (benutzt, frei)`). `typeexpr` (:137) kennt
// kein Tupel; der Ausweg waere ein `structty` — und den kann eine Funktion nach «B7» nicht
// HERSTELLEN, weil es kein Verbundliteral gibt. Zwei Befunde, die einander blockieren:
// deshalb hier zwei Funktionen und eine doppelte Traversierung.
// «B6» `ensures benutzt + frei == s.len` benennt Rueckgabefelder. Es gibt keine Bindung
// fuer den Rueckgabewert; oben behilft sich die Zeile mit dem Funktionsnamen, und das ist
// geraten, nicht geschrieben.
impl fn messen_benutzt(s : ptr<normal, r+own> Stack, art : Stackart) -> u64
    requires  s.len >= 8
    effects   { reads s, writes tiefe_max, writes gemessen }
{
    let frei = unberuehrt(s);
    // Das kommt durch, weil das `ensures` von `unberuehrt` `<= s.len` sagt: aus dem VERTRAG
    // der gerufenen Funktion, nicht aus einer Flussregel. Kostet eine Zeile Nachbedingung,
    // keinen Beweis.
    let benutzt = s.len - frei;
    // «B21» hier stuenden `accumulate tiefe_max by benutzt;` und `accumulate frei_min by frei;`
    return benutzt;
}

// «B22» `claim` nimmt eine Zeichenkette, und `char` (:95) schliesst `newline` aus. Alle drei
// echten Behauptungen sind mehrzeilig; hier zusammengezogen. Eine Behauptung, die in eine
// Zeile passen muss, wird kuerzer geschrieben, nicht genauer.
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
        // «B14» `let g = groesse else (e) { return false; };` ist nicht schreibbar: die
        // `let … else`-Form (:316) verlangt RECHTS einen `call`. Ein `option`-wertiges
        // `place` laesst sich damit nicht auspacken — und ein Atomic ist ein `place`.
        let g = groesse_gemessen() else (e1) { return false; }
        let f = frei_min_gemessen() else (e2) { return false; }
        if f < g / MIND_RESERVE_NENNER { return false; }
        // **Zweite Fassung, 2026-08-19 («H2.2»).** Hier stand:
        //
        //     return (g - f) + irq.tiefe_max + g / MIND_RESERVE_NENNER <= g;
        //
        // `PFLICHTEN.txt` fuehrte dazu die Pflicht *„`(g - f)` unterlaeuft nicht"* mit der
        // Begruendung *„`f < g / N` gibt `f < g` nur ueber die Division; die V-Regeln rechnen
        // nicht."* **Nachgerechnet: die Begruendung beschreibt den falschen Zweig.** Der
        // Vergleich steht in einem `if`, das ZURUECKKEHRT -- auf dem Weg hierher gilt
        // `f >= g / N`, eine UNTERE Schranke, und `g - f` braucht eine obere. Keine
        // schaerfere V-Regel schliesst das.
        //
        // Die Aussage ohne Subtraktion ist unter `f <= g` aequivalent und hat keine
        // Unterlaufpflicht. **Die Pflicht war ein Artefakt der Schreibweise, nicht der
        // Sprache** -- dieselbe Klasse wie `revoke` (200 zugesagt, 16 452 480 gerechnet):
        // *ein Mensch hat den typischen Fall geschrieben statt die Schranke.*
        return irq.tiefe_max + g / MIND_RESERVE_NENNER <= f;
    }
    floor    gemessen_tod >= MIND_MESSUNGEN, groesse >= 1, irq.n >= 1
    counterprobe "Fuellung ausgehaengt" expects erschoepft_waechst
}

}
```

**Verdict at the freeze: fits with findings** — B2, B6, B7, B14, B21, B22, B30. `check` would
hit exactly: its `measures` list *is* the report line (three hand-kept copies in the Rust),
`floor` hits the three speech tests `urteil()` conducts by hand, `gates kstack` is the linear
chain the original keeps as a voluntary first conjunct. What did not carry was the measured
quantity: no atomic read-modify-write (B21), and no `option` as a type (B14). Both closed.
**Today:** pierced. Its `narrow` at the traversal counter is the one *ritual* site of the corpus
(§8): its `else` branch can never be taken, because the bound falls out of the domain — a
place where M1 does not see what the human sees.

---

# F7 — Loader/bringup: the boot path with `BootPhase` as a value

**Origin:** `kernel/src/main.rs` (Caprock `a1bf707`). The original keeps its ordering *in
comments*; seven sites carry the sentence that explains each: before the MMU, atomics and
spinlocks are not well defined (single-core); cap tables before the first cap; IPC tables
before the first endpoint; report the authority document before starting the root task; the
verifier must stand before the root task; AP entry; a slab call only at boot. Site 4 is a
paid-for mistake: *"precisely this line was missing on ARM"* — the order stood as a comment in
one architecture and was absent in the other, and no tool could say so.

```gabbro
module caprock::bringup {

// Die Marke ist LINEAR: sie entsteht einmal, wandert durch die Strecke und wird am Ende
// verbraucht. Ein Weg, der sie fallenlaesst, ist ein Bootpfad, der nie fertig wird; einer,
// der sie verdoppelt, sind zwei Kerne, die beide glauben, sie booten allein.
linear ghost type BootPhase;

// `roh` heisst: vor der MMU. Atomics sind hier nicht wohldefiniert, also ist die Konsole
// sperrfrei -- und das ist eine EIGENSCHAFT DER PHASE, nicht des Geraets.
extern fn melde_roh(text : ptr<code, r> Text) -> u32
    requires  Held(PHASE_ROH)
    effects   { reads text } costs <= 64 ops;

// «B37» -- DER BEFUND DES FRAGMENTS. Die Marke traegt die Reihenfolge, aber sie traegt sie
// als LINEARITAET, nicht als ORDNUNG: `mmu_an` verbraucht die rohe Phase und gibt die
// gewoehnliche zurueck. Damit ist „vor der MMU" und „nach der MMU" unterscheidbar --
// **aber „Cap-Tabellen vor dem ersten Cap" ist es nicht**, denn beide liegen in derselben
// Phase. Fuer die vier Reihenfolgezwaenge INNERHALB einer Phase braucht es entweder je
// eine eigene Marke (dann waechst der Wortschatz mit jedem Bootschritt) oder eine
// Ordnung auf Marken -- und die gibt es nicht.
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

// Der Root-Task VERBRAUCHT die Marke endgueltig: danach ist der Bootzustand vorbei, und
// kein Pfad kann noch etwas tun, das nur waehrend des Boots erlaubt war.
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

**Verdict: the token carries — at seven sites, against a gate of five.** The yield is what it
does *not* carry: a linear token makes *before the MMU* distinguishable from *after*, but says
nothing about the order of four constraints inside one phase (**B37**: linearity enforces
*exactly once*, not *in this order*). B37 was closed by an order on tokens
(`order { … }` / `advances`). Pierced (`123456`).

---

# F8 — Scheduler: `Stale(T)` carried refutably

**Origin:** `kernel/src/system.rs`, `crates/caprock-sched/src/lib.rs`. The candidate: a
construct that replaces double acquisition (select under lock A, release, continue under B,
**re-check the finding**). Measured: **five values** cross a lock boundary in the scheduler and
are used afterwards under another lock.

| # | Value | Carried by |
|---|---|---|
| 1, 2 | `tid` to `kill` | `resolve(tid)` revalidates — exactly the pattern |
| 3, 4 | `tid`/`caller` from `current_id` | **counterexample:** IRQs are masked in the trap, so the current thread is stable across the short locks — no revalidation, and a *different* promise carries it |
| 5 | `bekommen` from `priority_of` | self-test path; the value is reported, not used |

Two of five — the hottest path, `exit_current` and the IPC handover — would be made unwritable
by an enforcing `Stale(T)`. **B38:** the honest form is *re-check or name what carries it
instead*, and the carrier `masks IRQ` counts only if the entry context says `nested masked`
(`entrydecl` already carries `nested ( "never" | "masked" | "bounded" constexpr )`), otherwise
the carrier is an escape hatch (the same assurance-satisfied-because-nothing-happened as R15).

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

// Der Fall, der TRAEGT: der Wert ueberquert die Grenze, und die Fortsetzung prueft neu.
// `resolve` ist genau die Neuvalidierung; ohne sie waere `toeten` ein Rennen.
extern fn aufloesen(l : ptr<normal, r> Laufliste, t : FadenId)
    -> option index into Laufliste
    requires Held(SCHEDS, shared)
    effects  { reads l.slots } costs <= 8 ops;

impl fn toeten(l : ptr<normal, rw> Laufliste, t : FadenId, k : index into Laufliste) -> bool
    effects { reads l.slots, writes l.slots, locks SCHEDS }
    costs   <= 340 ops
{
    locks SCHEDS {
        // **Die Neuvalidierung.** Der Faden kann zwischen Auswahl und Tat verschwunden
        // sein; `aufloesen` sagt es, und der `match` zwingt beide Ausgaenge.
        match aufloesen(l, t) {
            Some(i) => { l.slots[i].belegt = false; return true; }
            None    => { return false; }
        }
    }
    return false;
}

// «B38» -- DER FALL, DEN DIE ZWANGSFASSUNG UNSCHREIBBAR MACHT.
// Der Wert ueberquert dieselbe Grenze und braucht KEINE Neuvalidierung, weil eine andere
// Zusage ihn traegt: die Interruptmaskierung. `masks IRQ` ist in Gabbro bereits eine
// Wirkung -- die Begruendung steht also schon in der Sprache, sie ist nur nicht mit der
// Sperrgrenze verknuepft.
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

**Verdict: `Stale(T)` in the proposed form is refuted. New constructs: 0.** What remains is a
condition on existing constructs, not a word. Pierced (`1 1 1 0 0 1 1 1`).

---

# F9 — MMU/page tables: the entry that is pointer **and** bitfield

**Origin:** `crates/caprock-hal/src/x86_64/mmu.rs` (1 719 lines). The descent is four-level and
reads two things out of the *same* 64-bit number: `e4 & MASK` is an address, `e4 & P`, `& RW`,
`& US`, `& NX` are rights bits — nine named ones, two of them (`A`, `D`) *set by the hardware,
never by us*.

```
mmu.rs:578   let e4 = PML4.0[((va >> 39) & 0x1ff) as usize];
mmu.rs:582   let e3 = table_mut(e4 & MASK)[((va >> 30) & 0x1ff) as usize];
mmu.rs:589   let e2 = table_mut(e3 & MASK)[((va >> 21) & 0x1ff) as usize];
mmu.rs:596   let e1 = table_mut(e2 & MASK)[((va >> 12) & 0x1ff) as usize];
```

That was the finding that demanded the eighth domain, `mappings of`, answered with
`walk`/`embeds`.

```gabbro
module caprock::mmu {

const EBENEN   : u32 = 4;
const EINTRAEGE: u32 = 512;

opaque type Pa = u64;
type Idx   = u32 in 0 ..< EINTRAEGE;
type Ebene = u32 in 0 ..< EBENEN;

// **Der Eintrag ist EIN Wort mit zwei Lesarten**, und `embeds` sagt welche. Ohne die
// Zeile stünde die Adresse als blanke Zahl da, und `& MASK` wäre Konvention.
format Pte @version 1 endian little {
    roh : u64 embeds [51:12] scale 4096,   // der Rahmen: Bits 51..12, mal 4096
}

// Die neun Bits, einzeln benannt. `A` und `D` schreibt die Hardware -- sie stehen als
// `reserved`, weil ein Schreiben von uns ein Fehler wäre.
device Seitentabelle(basis : Pa) at normal {
    reg EINTRAG : u64 @0x0 class rw fields {
        P @0, RW @1, US @2, PWT @3, PCD @4, A @5, D @6, PS @7, NX @63,
    }
}

// `walk` erzeugt die Domäne `mappings of`: je Abbildung stehen `va`, `level` und
// `index[level]` bereit. **Die vierstufige Kette wird damit EINE Traversierung**, und ihre
// Schranke fällt aus der Deklaration statt aus einer Zählung im Rumpf.
walk Seitenabstieg levels EBENEN {
    node : [Pte; EINTRAEGE],
    down : roh when EINTRAG.PS == 0,
    leaf : EINTRAG.PS == 1,
}

// Die Schranke faellt aus `levels` mal `node`-Laenge: 4 Ebenen zu 512 Eintraegen.
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

**Verdict: fits — and the finding is what did NOT show up. New constructs: 0.**

**B39 — the two bits the hardware writes.** `A` and `D` are set by the MMU itself: in the
effect computation a writer no `effects` line names, so the frame statement *only what stands
there changes* is false at this site — not through a gap in the checker but because the
hardware is a participant. The honest form is an assumption with a falsifier, and one of the
few cases that really belong in the axiom layer. It also collides with the write-rights
promise as soon as group `ops` reach the page machinery (the K condition demands that *all*
write sites be generated, and the MMU is not a generated operation), so the exception would
have to stand at the declaration. The candidate was:

> ```gabbro
> walk Seitenabstieg levels EBENEN {
>     node : [Pte; EINTRAEGE],
>     down : roh when EINTRAG.PS == 0,
>     leaf : EINTRAG.PS == 1,
>     -- die Kandidatenzeile: `hardware A, D;`
> }
> ```

*A candidate, not a decision; it would be a new word and burden the convergence bet.*

**Completing it cost the excerpt a promise.** `mappings of` has meant the *leaf set* since
2026-08-20, which makes the excerpt's `costs <= 4096 ops` recomputably **false** (the body
costs 137 438 953 472); the two statements — about the set and about one entry — were
separated in the completed copy (`rechte_pruefen`, `costs <= 5 ops`), and the `device …
at normal` block became a `format` for the same word. `traverse … over mappings of` still has
no lowering: it needs a generated descent *and* a named resolver from frame to node, and there
is no place in Gabbro to write the resolver (the hand-written driver holds it). Pierced
(`1 2236416 0 1 0 0`; the poison inverts `leaf` and moves the number to `1118208`, so the value
provably comes out of the descent).

---

# F10 — Parser/checkpoint: the buffer nobody believes

**Origin:** `crates/caprock-dtb/src/lib.rs` (145 lines) — the only parser of the kernel that
reads foreign bytes. `Dtb::parse` reads a magic word and two offsets, and *every* access goes
through `be32(data, n)?`, a function that yields `Option`:

```rust
if be32(data, 0)? != MAGIC { return None; }
let off_struct  = be32(data, 8)?  as usize;
let off_strings = be32(data, 12)? as usize;
```

That is the range obligation, written out as control flow, at every access individually.
`format` takes exactly that off one's hands: the reader checks the buffer length once at
entry, and everything after is a proved access.

```gabbro
module caprock::dtb {

const MAGIE : u32 = 0xd00dfeed;

// Der Kopf ist ein FORMAT: feste Breiten, ausgesprochene Bytereihenfolge, und die
// `where`-Klausel bindet jeden Versatz an die Pufferlaenge. **Danach braucht kein
// einziger Zugriff mehr eine Laengenpruefung.**
format DtbKopf @version 17 endian big {
    magie       : u32 where magie == MAGIE,
    gesamtlaenge: u32,
    off_struct  : u32 offset_into Self where off_struct + 4 <= lenof(Self),
    off_strings : u32 offset_into Self where off_strings + 4 <= lenof(Self),
}

// Die Tiefe ist ein Zaehler, und die Zaehlerregel gilt: Schranke in der Deklaration UND
// Pruefung vor der Rechnung. Ein DTB mit 2^32 verschachtelten Knoten ist kein Baum mehr,
// sondern ein Angriff -- und die Schranke sagt das, statt es zu hoffen.
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

// **Der Zeuge, und bis 2026-08-18 stand er nicht da.** `progress` nennt eine Annahme mit
// Falsifikator; ohne `assume` steht der Name in keinem Manifest. `S003` hat es gefunden.
assume token_verbraucht
    "Jeder Durchgang verbraucht mindestens ein Token, und ein DTB hat endlich viele."
    falsifier sonde_dtb_endlich;

}
```

**Verdict: fits — new constructs 0 — and the finding is the place where the original already
writes Gabbro:** the rule exists, it just stands at every access instead of once at entry.
**B40 goes against the folder:** the original checks error-free over 145 lines with neither a
language nor a tool; a parser that fulfils its range obligations individually anyway gains
*brevity* from `format`, not *safety* — a real gain, and not the one the thesis promises
(base rate behind `format`: 5 formats in the whole tree, 0 occurred errors of that class, one
documented near miss; see `MESSUNGEN.md`). Pierced (`1 0 0 0 0 65`).

---

# «F0» — the floating-point corpus, and it overturned a plan decision at once

*Measured 2026-08-18 on a floating-point-heavy renderer (Fraktaler 3.1): 52 source files,
479 `float`, 355 `double`, 37 `long double`, 128 NaN/Inf sites, and no fast-math flag in the
makefile of a performance-critical program. Caprock has no computing floating point at all;
a corpus for floats had to come from outside, or the design would be for an imagined use.*

**FF1 — the escape test.** Four of the seven float decisions in two lines of real code: the
programmer writes the NaN check *by hand beside the comparison* (because `Zz2 < ER2` alone does
not cover it), plus a clamp (that is `narrow`), a width mix (`float` from `double`, explicit),
two libm calls (the axiom layer) and an *inexact literal*.

```c
float t = float(arg(Z1)) / (2.0f * 3.141592653f);
if (Zz2 < ER2 || isnan(de.x) || isinf(de.x) || isnan(de.y) || isinf(de.y))
```

**FF2 — the precision ladder answers the `long double` question.** Where extra precision is
really needed, `long double` is *one rung of seven*; above it sit `floatexp`, `doubleexp`,
`softfloat`, `float128`, all software types of the program. Whoever needs more than `f64` wants
a *named* precision, not a platform-dependent 80-bit type, so refusing `long double` reads off
what real programs do anyway.

```c
= { "none", "float", "double", "long double", "floatexp", "doubleexp", "softfloat"
#ifdef HAVE_FLOAT128
  , "float128"
#endif
};
```

**FF3 — the reduction.** A sum over an array is `accumulates` — and over floating point it is
order-dependent, while `accumulates.monoid` is proved under the premise that it is not. The
corpus supplies the demand evidence for `F004`: the refusal is not precautionary, it hits a
form that occurs.

```c
progress_t a = 0;
for (count_t i = 0; i < count; ++i) { a += progress[1 + count + i]; }
```

**FF4 — the literal measurement, which overturned rule F1.5.** All 340 float literals against
*is it exactly representable?*:

```
340  literals in total
287  exactly representable   (84 %)   -- 0.0, 1.0, 2.0, 3.0, 0.5 …
 53  NOT exact               (16 %)   -- 0.6931471805599453, 6.283185307179586, 0.04045, 4.1
```

The planned rule *exact or refuse* would have refused 53 literals including ln 2 and 2π — an
unusable language, since a transcendental constant is exact in no binary width. The rule that
the measurement supports forbids the *silently* inexact, not the inexact: **declared or
refused**, spelled with one word that has a sibling in the folder (`u32 wrapping` says
*overflow is declared, hence no finding*; `rounded` says the same about rounding):

```gabbro
const TAU : f64 = 6.283185307179586 rounded;
```

`rounded` is in the grammar today (`fexpr = float [ "rounded" ]`, compulsory at an inexact
literal). What F0 contributed: F1.3 (the hand check beside the comparison) confirmed as real
code; F1.5 overturned; `long double` refusal as a reading, not a hardness; `F004` evidenced;
no fast-math in a performance-critical renderer.

---

# «K2» — a second corpus from a foreign author line: the Linux kernel tree

*2026-08-18. The aarch64 lesson was: a corpus the same author writes for the same language
measures fit, not transferability. Counts over `kernel/` and `mm/` (234 of roughly 64 000
files); no foreign code was copied into this repository.*

```text
spin_lock  808     mutex + rcu_read_lock  571     atomic_*()  637     per_cpu  411
barriers / *_ONCE  589     allocations 938     BUG_ON / WARN_ON  2034     goto  2669
unbounded loops  74
```

The two largest numbers are the two claims of the folder, at foreign code for the first time:
`BUG_ON`/`WARN_ON` (2034) are run-time assertions — the class Gabbro *replaces* by M1 facts —
and `goto` (2669) is the commonest control-flow form of the tree, which Gabbro lacks on
purpose. `goto` splits into four Gabbro forms and three exist: error labels (`out`, `err`,
`error`, `fail`: 1 147) become `let … else`; unlock labels (`out_unlock`, `unlock`: 220)
vanish because a `locks { … }` block takes and gives on every path ("the target does not exist
because the problem does not"); `retry` (90) becomes `retry … bounded N ops … on_exceeded`;
`next` (54) is `next`. **The construct-level find was RCU** (578 lock/unlock sites, 73
dereferences, 99 grace-period calls): the read side takes *nothing*, the write side swaps a
pointer and waits for a grace period, so Gabbro's lock model (mutual exclusion) had no word for
it. A corpus that only confirms measures fit; this one showed a class the language did not
know. RCU is now in the grammar (`rcu D protects { … } reclaims p;`, `observes`; the grace
period is an `assume`).

*Counting forms is not translating them.* Five fragments were cut and run through the
checker — reproductions, not translations: the tables are invented where `struct bsd_acct_struct`
was not cut along.

**K2-F1 `setpriority`** — two jump labels, the first exists only to release. In Gabbro the
labels do not appear: `locks`/`rcu` ends with the block, the error path is `match`. 0 errors.

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

**K2-F2 `acct_get`** — `goto again` *is* a `retry`, with a bound and a named overflow that the
original lacks (its loop is unbounded and spins forever if the counter never frees);
`rcu_read_unlock` stands three times, once per exit — exactly what a block makes unnecessary;
and **M1 found, on the first run, an overflow the original does not check**:
`atomic_long_inc_not_zero` guards against zero, not against the upper bound.

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

```
die Zuweisung requires `u32 in 0 .. 65535`, the value has `u32 in 2 .. 65536`   -- M101
```

The answer is in the same language — a second bound in the `if`, and the checker is silent. The
reconstruction with RCU replaced by a lock checks clean:

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
            // **Die Schranke, die das Original nicht hat.**
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

**0 errors, 0 hints** — one missing construct blocked both fragments and the rest carried: lock,
rank, hold time, bounded retry, named overflow, progress assumption with falsifier, index
bound. After RCU, one remnant: the original's `atomic_long_inc_not_zero` is its own mutual
exclusion, while in Gabbro `atomic` is an *item and not a slot field*, so a counter inside the
object cannot be declared atomic and `H010` demands a lock the original does not need — a
finding about the language, still open.

**K2-F1 after RCU** — both labels disappear (the scope ends with the block, the error path is
`match`):

```gabbro
observes TASKLIST {
    match nutzer_suchen(wer) {
        None    => { return 1; }
        Some(i) => { return Prozesse.slots[i].nice; }
    }
}
```

**K2-F3 `sum_mthp_stat`** — thirteen lines become one declaration; the order independence the
loop silently relies on is *proved* (`accumulates.monoid`):

```gabbro
accumulates mthp_summe : u64 merge add per cpu 64;
```

**K2-F4 `pid_namespace`** — the progress witness stood as a comment:

```c
	/* Once all of the other tasks are gone from the pid_namespace
	 * free_pid() will awaken this task. */
	for (;;) { … schedule(); }
```

The comment *is* the assumption; Gabbro turns it into a declaration with a falsifier and adds
the per-pass bound and the named overflow the original lacks:

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

**K2-F5 `BUG_ON(addr >= end)`** — the same line three times in one file. In Gabbro the statement
stands in the type and the relation is checked **once**, with a named exit; and the counter-probe
is the measurement itself: remove the comparison and the subtraction falls:

```
`u32 in 0 .. 65535 - u32 in 0 .. 65535` leaves the width of the result type   -- M104
die Rueckgabe requires `u32`, the value has `u32 in -65535 .. 65535`          -- M101
```

The assertion is not believed, it is enforced at translation time — the `BUG_ON`/`WARN_ON`
target of 2034, on one case.

**Stand of K2:** five fragments, five classes (jump labels · retry · per-core sum · unbounded
loop · assertion); four carry with no remainder (F1, F3, F4, F5); F2 keeps one remainder (no
atomic inside a slot). Three finds no own corpus would have delivered: RCU as a class, the
counter overflow, the progress witness as a comment. And what this is not: five fragments are
no statement about 64 000 files, they are reconstructions, and the form is measured, not the
body. *Audit note (2026-09-04): «K2» is a second corpus from a foreign author line, but the
checker was extended for it 57 minutes after the fragments were cut, and the K2 blocks are
`cargo test` fixtures — it measures the rules it helped write. Of the four blocks of this
section only one whole module parses clean today, two blocks start mid-form.*

---

# The network stack — a corpus whose template comes from outside

*Ethernet → ARP → IPv4 → UDP echo, written against RFC 791, 826, 768 and 1071
(`messung/netz/udp-echo.gab`), and checked against **published** vectors, not packets of its
own: the classic IPv4 header of RFC 791 (checksum `b861`) and the RFC 1071 §3 example (sum
`ddf2`), with the counter-calculation from a second implementation written differently. The
rule is "no new construct without a program that needed it — and the template comes from
outside", otherwise a stack measures how well Gabbro fits Gabbro. Instrument:
the retired `zaehle-netz` (2026-10-17; not guarded today).*

Four holes that 45 clean examples did not show (the corpus is written *per construct*; a `!`
is not a construct, it is what one does when one writes a program):

1. **`!` had no lowering** — `if !kopf_gueltig(k, w) { return 0; }`, the most ordinary line of
   a receive path, passed the checker and was refused by the emitter. Built
   (`beispiele/46-verneinung.gab`); unary minus deliberately *not* (`gift/219`: in C, `-x` on
   an unsigned operand stays unsigned while M1 says `i32 in -4294967295 .. 0`, and no program
   needed it).
2. **The error channel `-> T or R` lowered wrongly in two ways at once** — `f(0)` reported
   failure for a valid value, `f(7)` left the result untouched (the generator wrote
   `return <value>;` into a `bool` function and added `const`, whereupon GCC dropped the store);
   0 checker errors, emitter exit 0, `cc` without `-Werror` compiles. Every `or R` in the
   corpus had stood on an `extern fn` — on bodies the generator never sees. The first Gabbro
   body with an error channel was this stack.
3. **A `reason` value had no producer** — now produced, and the emitted C says so.
4. **"Read the same bytes as big-endian 16-bit words" is not writable**: a `format` explains
   byte order for its fields, and a field type `[u16; 10]` is refused twice (the type and the
   access). The words are assembled in C, outside the language — precisely the step network
   code would need the language to manage.

And a hole found *by reading the stack's own code*: `echo_beantworten` takes `ptr<…, rw> IpKopf`
and `ptr<…, r> Kopfworte` over the **same twenty bytes**; the answer read through the second is
stale after `k.ttl = 64`, `effects` claims both accesses are declared, and the checker says
0 errors (only the same site on two `own` parameters falls, `R004`). The rights half is right;
**the event half is missing** (nothing invalidates the view at the write). The settled shape
(`SYNTAX.md` §3): one view writing, all others reading, and the switch is an event — the shape
of `state`/`transition` applied to views. A byte view that takes only the rights half inherits
the hole and gives it a construct to hide behind.

What this stack is not: no TCP, no fragmentation, no variable header length (`ihl > 5` is
checked, not handled), no timer; three vectors, not a network.

---

# What `H` measures, and what an audit of it left standing

**`H`** is the K100 gate "hanging plumbing obligations", read as `10 − |pierced fragments|`:
`H = 1` (F3) when last counted (2026-10-17, by the retired `zaehle-pflichten`; not guarded today). The obligation base was the retired `PFLICHTEN` register (239 obligations = 173 K plumbing +
66 L logic, assigned 2026-08-17 over F1–F10 plus one lowering row each; `L : K = 0.38 : 1`,
derivable with that counter). Its history, in three lessons:

* **The ratio is the wrong statistic, `H` is the measurand.** Over the Rust, `delete_leaf` was
  4 K / 7 L = 1.75 : 1; over the Gabbro fragment the same criterion gives 13 K / 8 L = 0.62 : 1.
  Gabbro did not *create* nine more plumbing obligations, it wrote them down (`Held(CAPS)`,
  `<= 200 ops`, the effects line, the `own` threading, call preconditions). A language that
  carries more plumbing explicitly gets a *worse* ratio and a *better* `H` — and only the second
  is the direction the thesis claims. Of the 173 K obligations 137 were carried by construction
  when `H` first read 36 (gate missed against a bar of 0); the trajectory to today's 1 was
  bought by construction and by corrections of wrong entries (B9, B21, B27 were false rows),
  each with a re-measurement.
* **A `narrow` is not one thing.** Of the three hand-written `narrow … else` sites in the
  corpus, one is a real check (F10, a hostile DTB takes the branch), one is the deliberate
  second net (F1, the bookkeeping invariant is what keeps the branch dead), one is a *ritual* (F6,
  the bound falls out of the domain and M1 does not see it). The measurand became
  `N_ritus = 0`; today it is a *judgement* (`N_ritus = 1`, the F6 site) and only the half that
  needs no judgement is measured: `N_folgenlos` — a `narrow` whose removal changes nothing —
  counted **0** (by the retired `zaehle-bereichspflichten`).
* **Zero plumbing among the refusals of F3, and an emitter refusal can be plumbing.** The
  classification of F3's 18 refusals by the pass that raises each: 0 plumbing, 9 *rule
  decisions* (the refusal is right and Gabbro would have to stop making it or gain a
  production: `N035` ×5, `M124` ×3, `M140` at `enqueue` for want of an address-of, `C001` at the
  queue traverse), 9 *the program is wrong* (six `M140`, `M143`, `M101`, `H011`: suppressing
  the refusal would only move the failure to `cc`, and a cast would make it compile by breaking
  the run). Five of the `N035` sit on a declaration the fragment never calls through. The same
  work refuted a criterion — "`gabbro pruefe` reports 0 errors ⇒ only the generator is
  missing ⇒ plumbing": the probe
  `messung/proben/probe-queue-traverse-checks-clean-and-has-no-lowering.gab` checks clean and
  `gabbro emit` still refuses it (`[C001]`, B10). *A criterion wrong in both directions is not a
  threshold that needs moving.* And `C001` is not automatically non-plumbing: `D21` (`retry`
  never pushed the loop label `forever` pushes) and `D22` (a record bound by `let … else`)
  were `C001` over an arm nobody had written, and only running `emit` tells the two apart.

**The adversarial audit of 2026-09-04 (four K100 gates) and the independent re-judgement of the
same day** left these standing:

| Gate | Verdict | What it means now |
|---|---|---|
| `H` | adds nothing beyond the retired `pruefe-emission`'s piercing ledger | `H = 10 − pierced`, over ten fragments chosen for difficulty — `H = 0` would still be trap 80 (a number a human runs parallel to the truth) until a corpus stands beside them that nobody looked at while building. `H` is a countdown, not a coverage measure; no code computes "100 % plumbing" |
| `L` (templates carried unproved) | the count holds, the gate did not exist | the bound `L <= 4` stood only in a comment; the test asserts today's value (`lebend_ungedeckt() == 2`). Two entries are contestable hand judgements (`gruppe.sperrabdruck`, `walk.mappings`) |
| second corpus «K2» | does not hold as independent | see the K2 section; and the guard labelled "second corpus" points at the same codebase as the Caprock base (a different checkout of Caprock) |
| `A_p` (falsifiable assumptions with a probe that stands as a program) | holds: `5 of 38`, floor `1/8` | the guard walked the *working tree* with `rglob`, so one untracked `.gab` outside four hard-coded directories broke it (exit 2); the class (walking the tree instead of `git ls-files`) was repaired for the named instance only. `instrumente/korpus.py` is the shared "is this file one `git` knows about?" check |

The headline *100 % plumbing coverage* does not follow from the four. What would make it follow:
a coded ratio over a mechanically derived source, an `H` that classifies by running `emit` and
reading *why* it refuses, an executable `L <= N`, and a second corpus assembled by a party that
did not write the fragments.

---

# The completion work, in findings (what `messung/fragmente/` taught)

Each completed copy states in its head what was added and what was not (declarations the excerpt
calls and does not name; nothing rewritten, nothing left out). Seven of the ten carried at least
one *corpus-side* bolt: 41 sites naming 20 undeclared names (`MAX_POLL`, `EP_BADGE`,
`SYSNO_RESULT`, `Fehler`, `NTFN`, `IpcResult`, …), nine `let … else` calling bodies the unit
does not know, six unnamed bit positions, one table without `tree`, one callee without `or
<reason>`. Where an error stood after completion it belonged to Gabbro, and that was the yield:

* **`A::B` parses and was never resolved** (`IpcResult::Ok` fell as `M119`).
* **A `reason` value had no producer** — superseded: `return R::F;` is settled as one of three
  permitted positions since stage 7; a reason value as a *call argument* was closed by the
  "fourth door" (2026-08-25).
* **A frozen corpus goes stale under a new refusal**: the five `fn(…)` lines of F3 would have to
  carry a contract that did not exist on 2026-08-14 (`N035`).
* **Refusals right for the wrong reason**: a `static` of a record type was refused for every
  initialiser although the text named only the case "initialised with an ordinary number"; it
  lowers now as a braced initialiser with designators (a compound literal is not a constant
  expression, C11 6.7.9p4).
* **A `check … can_fail` body was not entered by the name, effect and cost passes**: the same
  unknown call is `0 errors` inside a `check` and `E009` + `K003` inside an `impl fn` — and
  the quieter answer stands in the block whose purpose is measuring. Not built; booked.
* **The generator found its own errors behind refusals** — a defect behind a refusal is
  invisible for exactly as long as the refusal stands. F1's completion exposed two emitter holes
  (a `let … else` over a callee with an error channel and no result had no lowering; and the
  success `return` of an `or R` function was never written, so the C ran off the end of a
  non-void function — compiled under `-Wall -Wextra -Werror` at `-O0` and `-O2`, because
  `-Wreturn-type` does not reach a `static` function nothing has called yet). Only a *run*
  reads hole 2: the sharpest argument for counting Durchstiche instead of compilations.
* **Three kinds of "who was wrong"**: for F9, F1 and F5 the larger half of every repair was
  finding out which side was wrong, and each time it was the fragment, not the refusal;
  every one carried at least one checker or emitter defect behind the fragment's own error
  (`walk … levels` over a `const` name, the result-less `or R` call, `N046` reading a signature
  without its error channel). The vocabulary ratchet did not move once.

# Obligation-side measurements

*Hand-measured on this corpus; all numbers below stand next to the instrument that re-derives
them.*

* **How many obligations can a prover read (P6, 2026-08-21).** `gabbro pflichten` counted 47
  obligations over the example corpus (6 preservation, 10 postcondition, 11 foreign, 20
  precondition). Written as an Isabelle theory, **one** goes through; the other 46 are refused
  one by one with a reason: 12 are already carried by another pass, 11 are assumptions rather
  than obligations, 23 remain open. The one that passes is a K (index/overflow) obligation, not
  a W (value) one — so the channel exists (`gabbro pflichten --isabelle`/`--lean`,
  the retired `zaehle-p6`) but the corpus had no W obligation that fits it.
* **GabbroV population (2026-09-03).** Three `progress` rows are booked twice in the retired `PFLICHTEN` register
  (once as a logic obligation, once as an assumption: a `progress` name must resolve to a
  declared `assume`, `S003`/`S004`), and the emitted manifest does not double-book them.
  Rebooking them moves GabbroV's population 66 → 63; the K/L split of the retired `PFLICHTEN` register does not
  move (173 / 66), because that column is machine-versus-subject, not obligation-versus-assumption.
  The vacuity check (`programmlogik/gabbrov/V2.lean`, proved sound) over the 55 sayable
  obligations: 31 carry a precondition, 0 are vacuous, 24 have none; two of the 26
  quantifier-free ones (L44, L53) are tautologies. Of the 55, 26 are quantifier-free in shape
  (the ceiling for a certificate route through a solver), 29 need quantifiers, folds or
  reachability (`python3 messung/gabbrov/cert-theorien.py`).

| | before | after |
|---|---:|---:|
| GabbroV's obligation population | 66 | **63** |
| of those, not sayable | 10 | 8 |
| of those, sayable | 56 | 55 |

| Derived (2026-10-17) by the retired `zaehle-pflichten`; historical | |
|---|---|
| **GabbroV's obligation population** | **63** |
| of these, discharged by the assumption layer | 3 |

  The three rows with a figure were the ones the retired `pruefe-zahlen` read (they stood in the
  retired `messung/GABBROV-V2.txt`); the figures were derived by the counter above.
* **The obligation manifest versus its subject (E1).** The retired `pruefe-manifest`
  held every `obligation` line of the emitted manifest against the correspondence table
  the retired `PFLICHTEN-KORRESPONDENZ.txt` (one row per obligation of GabbroV's population):
  states CARRIED (a manifest line states it), BLOCKED (the fragment emits no register),
  DROPPED (a clause stands in the source, unbooked), NO CLAUSE (nothing in the fragment states
  it). As of 2026-09-04: 20 carried, 13 blocked (F03 only), 5 dropped, 25 no clause — a
  re-derivation after F01/F05/F09 became emitting; the first split `43 blocked / 15 dropped / 5
  carried` of 2026-09-03 was superseded because nothing derived it. *That table is a machine
  input: it stays a file of its own.*

# Audit sweeps (2026-09-01/02) — what stays true after the C emitter was deprecated

Two sweeps handed an output of the project to something that did not write it. Their findings
about the **checker's boundaries** hold whatever the back end:

* **Boundary arithmetic.** 15 declaration forms × 60 values, later 63 forms and 5 778 cases,
  each run in *both* build profiles (release has no overflow checks, and release is what
  `cargo install` produces: a disagreement catches a panic and a silent wrap at once). After the
  repairs: 0 disagreements. Found: `N049`'s extent arithmetic panicked in debug and wrapped in
  release (a lossy `as i128` on a `u128`, in code one day old); `N050` (the bank index multiply
  is 32-bit, so `F[65535].X` named a register 64 GiB below the declared one); `N051` (a layout
  number wider than the pointer arithmetic); `M139` (an integer literal wider than `i128` had no
  type, so every range rule went quiet: *"unknown" is not a refusal, it is an acquittal that
  reads like caution*); the emitter's own `as` cast wrote `vector -1` for `u128::MAX`.
  Lessons: a rule that is right because two errors cancel does not hold; a repair can carry
  the defect it was written beside; a message is code; and the sweep's own instrument was wrong
  before the tree was, three times, each caught by its speech test.
* **The emitted C under foreign tools** (gcc 16, clang 22, `clang --analyze`, UBSan/ASan over the
  24 units the emission guard drives end to end): zero findings except one real one — a null
  pointer constant dereferenced (`static tz : ptr<…> Platz = 0;`), repaired in the emitter
  because address 0 is a vector slot on bare metal. ASan runs only where its shadow map fits
  the kernel; elsewhere the stage prints "not run" and the number falls instead of staying.
* **Found and not repaired** (not re-probed since): `M103` does not run in predicate positions
  (`spec fn` body, `ensures`, table `invariant`); `aligned(p, 0)` and `aligned(p, 3)` are
  accepted; `table count 0`, `[u64; 0]` and `embeds … scale 0` are accepted by the checker; a
  65 536-character identifier is written into C. **Not swept:** 57 of 100 boundary-carrying
  rules, combinations of boundary slots, the emitter as part of the property; no `cppcheck`, no
  big-endian toolchain.

# Where the blocks moved

When this file was consolidated on 2026-10-17 the code blocks kept their bytes; their start
lines changed. If an old comment quotes a line of this file, add the shift of its block:

| Block | first code line before | first code line now | shift |
|---|---:|---:|---:|
| F1 | 91 | 161 | +70 |
| F2 | 396 | 453 | +57 |
| F3 | 567 | 622 | +55 |
| F4 | 766 | 806 | +40 |
| F5 | 943 | 978 | +35 |
| F6 | 1071 | 1103 | +32 |
| F7 | 1340 | 1280 | -60 |
| F8 | 1469 | 1364 | -105 |
| F9 (first block) | 1563 | 1442 | -121 |
| F10 | 1684 | 1543 | -141 |
