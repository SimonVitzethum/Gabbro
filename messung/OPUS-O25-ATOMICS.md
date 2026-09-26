# Opus lane O25 — unguarded atomic communication over machine W (2026-09-26)

*Branch `worktree-agent-addcada38733de2a3` on master `9ed1b5d7` (the weak memory model of Opus
agent B). Task: OFFEN O25 (a rely for unguarded atomic reads), O17's read half, O26 (memory
orders of own lock primitives). Everything measured on this machine through the queued wrappers
(`./lean-bau`, `./lean-probe`, `./cargo-pruef`, and `cargo build` through the cargo slot).*

## 1. Result in one paragraph

The task does not fit whole, and the part that does not fit is named exactly. **Proved,
standalone (no `Spec.lean` definition moved):** with the footprint check exempting ATOMIC
carriers only, every step of the weak machine W is a step of a machine GA — G on a memory that
agrees with G's at every non-atomic carrier, the atomic reads answered per W (coherent,
release/acquire views) — so plain carriers stay sequentially consistent while atomics race
(`schwach_ist_gA`); the release/acquire hand-off of views is a theorem on every program
(`hb_uebergabe`); and on every program the relaxed checker `AkzeptiertA` accepts, the legs of
`Ziel` that the LANGUAGE carries hold at every machine W reaches — trace invariant, lock
exclusivity, no deadlock, no wait cycle, time — and race freedom holds for every plain carrier on
every W run (`w_sprache_akzeptiertA`). Witnesses: the flag (W's stale read really happens on an
`AkzeptiertA` program and is covered), the per-core fold, a refused plain payload read, and a
`fetch_add` counter that is 2 on an atomic-RMW view machine — while W itself can lose the update.
**Rust:** O26 closed for own primitives — `N481`–`N483` demand an acquire at the take, a release
at the give, and both on one word. **Not reached:** the CONTRACT legs over GA. They come from the
replay of the user's sequential proof (`execEndH`) into G, which needs a rely (a havoc at a shared
atomic read) through the whole replay family (~30 000 lines); without them a `GabbroZiel` over
`AkzeptiertA` would lose legs, so the goal statement keeps `Akzeptiert` and no Spec diff was made.

## 2. Design

**The rely, split in two.** O25 named one route: `execEndH` answers a shared atomic read with an
arbitrary value, `fuss` exempts atomics, the replay carries the havoc. It has two halves that can
be separated:

1. **Memory half** — what W presents to a step when atomics race. Machine GA
   (`RufSchrittGA`, `Speichermodell/Atomar.lean`) is exactly "G with a havoc at every atomic
   read": a G step on a presented memory `σ` that equals G's memory at every carrier that is
   not an `atomic` global; the successor takes the written carriers from the step and keeps the
   rest (W's own bookkeeping, `SchrittW.speicherS/U`). The theorem to prove: under the relaxed
   footprint property `FussSA`, every W step is a GA step, i.e. W's weakness is confined to the
   atomics.
2. **Logic half** — that the user's proof covers every value a GA step may present at an
   atomic. That is `execEndH` with the havoc plus the replay; §6.

**Why this is the right shape.** The DRF invariant `SichtInv` of `DRF.lean` needs, at a read,
that the reader's view is at the newest message. For a plain unguarded carrier that follows from
thread-locality (`FussS`), for a guarded one from the lock views. `FussSA` keeps both demands for
every NON-atomic carrier; the invariant is restricted accordingly (`SichtInvA`: `frei` and
`stimmt` over non-atomic carriers). The one thing that breaks is `erreicht`: W's G-part is no
longer G-reachable (a stale atomic read changes control flow). The static facts the DRF proof
used — the trace invariant, the frame read bound, the feature invariant, lock exclusivity — are
all properties of the THREADS, never of memory, and every G step lemma is generic in the machine.
So they hold on every GA run (`gaInv`), and every lemma that asked for G-reachability is re-proved
from them (`zugriff_haeltA`, `schritt_zugriffeA`, `lies_faktenA`, `frei_schreiberA`).

**Publish/await.** The view transfer is W's construction: a release write stores the writer's
view in its message (`schrittW_freigabe`), an acquire read joins it (`schrittW_erwerb`), views
grow and messages persist along runs (`laufW_waechst`). `hb_uebergabe` composes them: after `u`
acquire-reads the message `t` released, every later read of `u` at any other carrier returns a
message at or above `t`'s view before the release. That is the happens-before a payload read
needs. What is NOT built is the footprint rule that would admit a PLAIN payload read after an
`awaits` (it needs flow facts: the producer writes the payload only before its `publishes`, the
consumer reads it only after its `awaits`); so a plain payload read across threads stays refused
(`nutzlast_ohne_erwerb_abgelehnt`), as in verdict P3.

**RMW.** W's step lets a step that reads and writes one atomic (`exchange`, the only RMW form)
write at any fresh timestamp above its view — not adjacent to the message it read. That admits
the lost update RC11 forbids (`zaehler_verloren`). An atomic RMW writes at the read message's
timestamp + 1 (`ZSchritt`, `Speichermodell/Zaehler.lean`); there the counter is a theorem
(`zaehler_zwei`). Adding the adjacency to `SchrittW` changes the machine `Spec.lean` imports — a
Spec-relevant change, not made (§6).

## 3. What is proved (every `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`, or fewer)

| file | theorem | statement |
|---|---|---|
| Atomar.lean | `FussSA`, `fussSA_of_fussS`, `getrennt_of_freiA` | footprint property with the atomic disjunct; the old one implies it; an unguarded NON-atomic footprint carrier is thread-local |
| | `RufSchrittGA`, `RufErreichbarGA`, `ga_aus_g` | machine GA; every G run is a GA run |
| | `gaInv`, `gaInv_spur`, `gaInv_orte`, `gaInv_merk`, `gaInv_exklusiv` | thread-only invariants on every GA run |
| | `SichtInvA`, `schritt_sichtInvA`, `sichtInvA_erreichbar` | the view invariant with racing atomics |
| | **`schwach_ist_gA`**, `plain_liest_neueste`, `ga_aus_w` | every W step a GA step, presented memory = G's at every non-atomic carrier; a plain read is the newest message; W runs project to GA runs |
| | `w_spur_exklusiv`, `schwach_ist_gA_vor` | trace invariant and exclusivity over W; the old theorem is the special case |
| | `schrittW_freigabe`, `schrittW_hist`, `laufW_waechst`, **`hb_uebergabe`** | the release/acquire hand-off, every program |
| | `schrittGA_zerlegen`, `LaufGA`, `sperre_ordnetGA`, **`rennfreiGA`** | race freedom for non-atomic carriers on every GA run |
| AtomarZeuge.lean | `fussWAB`, `fussWAB_iff`, `AkzeptiertA`, **`akzeptiertA_of_akzeptiert`** | the Bool, the relaxed checker, the embedding |
| | `akzeptiertA_ok`, `schwach_ist_gA_akzeptiert` | the checker gives the memory theorem's premises |
| | `gaInv_rang`, `kein_warteZyklusGA`, `keine_verklemmungGA`, `LaufW`, **`w_sprache_akzeptiertA`** | the language-carried legs over W (see §1) |
| | `n1_akzeptiertA`, `n1_start`, `n1_ga`, `n1_sprache`, **`n1_nicht_sc_aber_ga`**, `n1_schwachSC_falsch` | the flag witness |
| | `faltung_abgelehnt`, `faltung_akzeptiertA`, `faltung_echt` | the per-core fold |
| | `nutzlast_ohne_erwerb_abgelehnt`, `nutzlast_echt` | the refusal |
| Zaehler.lean | **`zaehler_zwei`**, `zaehler_lauf`, **`zaehler_verloren`** | the counter: 2 under atomic RMW, lost update under W's shape |

**Witnesses, non-degenerate.**

- **Message passing / the flag.** Configuration 1 of the noninterference fixture: `kern` stores
  the atomic `konfig`, `hauptA`/`hauptB` read it into their plain tables, no lock.
  - It is refused by `Akzeptiert` (`n1_abgelehnt`) and accepted by `AkzeptiertA`
    (`n1_akzeptiertA`).
  - W's stale read `w_nicht_sc` (after `kern` wrote 3, `hauptA` reads the initial 0 and stores 0
    where G stores 3) happens ON this accepted program, and it is a GA step
    (`n1_nicht_sc_aber_ga`).
  - On every W run of it, every step is a GA step with both plain tables presented as G's
    (`n1_ga`), and the language-carried legs hold (`n1_sprache`).
  - The general release/acquire hand-off is `hb_uebergabe`; the litmus form over the instruction
    machine is `mp_ra_verboten` (§50).
- **Counter.** `zaehler_zwei`: on every complete run of the atomic-RMW view machine the newest
  message holds 2; `zaehler_lauf` shows such a run exists; `zaehler_verloren` shows the lost
  update under W's shape.
- **Per-core fold (O17 read half).** `zaehlA` twice (a pool writing the atomic `zaehler`) plus
  `zaehlB` reading it: refused by `Akzeptiert`, accepted by `AkzeptiertA`; `faltung_echt` pins
  that the fold really reads what the pool writes. Covered by the memory theorem and the
  language-carried legs, not by the contract legs.
- **Refusal.** `hauptA` writes the PLAIN `tabA`, `zaehlA` reads it with no lock: `AkzeptiertA`
  refuses at its footprint component (`nutzlast_ohne_erwerb_abgelehnt`); `nutzlast_echt` pins
  the shape.

## 4. The Spec diff review (AGENTS §2)

**No definition of `Spec.lean` moved.** `GabbroZiel`, `Ziel`, `AkzeptiertSpec`, (b), (c), (d)
are unchanged; `gabbro_ziel` is untouched, and `#print axioms gabbro_ziel` is
`[propext, Classical.choice, Quot.sound]` (measured through `grammatik/NachpruefungZiel.lean`
after the final build).

**Two comment-only corrections to the header**, both reviewed here as a diff:

| where | before | after | why |
|---|---|---|---|
| assumption (3) of the reading | own primitives: "`N323` … NOT the memory orders … follow-up OFFEN O26" | own primitives: `N323` plus `N481`–`N483`, orders CHECKED at the source level, their lowering staying assumption (2); foreign ones ASSUMED; the `N042` measurement (no accepted program has a non-driver lock primitive today) | the old sentence became false with `N481`–`N483`; leaving it would be a stale named assumption |
| NOT CLAIMED, the O25 line | "covering them needs … a rely, OFFEN O25" | the same, plus a pointer: the MEMORY half is proved standalone (`schwach_ist_gA`), the replay is what is missing | honest scope, no new claim inside the statement |

**The diff that O25 needs and that was NOT made** (so that the next lane does not have to find
it):

1. `C.akzeptiert` decides `AkzeptiertA`'s components: `AkzeptiertSpec.fuss` over `FussSA`.
   A RELAXATION of (a), so every old checker stays a `Pruefer` and every old program keeps its
   verdict (`akzeptiertA_of_akzeptiert` is the Bool half of that embedding).
2. `LogikPflicht` over `execEndH` with the atomic havoc. A STRENGTHENING of (b) for programs that
   read shared atomics; for a program whose atomic reads are all local or guarded the havoc is
   the identity (the embedding lemma to prove, like `execStmtH_leer`).
3. The leg `schwach` in GA form: "every W step is a GA step, plain carriers SC"
   (`schwach_ist_gA`). `SchwachSC` itself is FALSE on accepted flag programs
   (`n1_schwachSC_falsch`), so keeping it and relaxing (a) would make the goal unprovable.
4. Every other leg re-proved over GA runs. The language-carried ones already are
   (`w_sprache_akzeptiertA`); the contract ones need the replay (§6).

Making 1 and 3 without 2 and 4 would be a partial Spec change — forbidden by the task and by
AGENTS §2 — so none of them was made.

## 5. Rust (OFFEN O26)

`namen.rs::sperrprimitiv_ordnung`, sentence `namen.sperrprimitiv_ordnung` (`saetze.rs`). The
facts of `N323`'s fold now carry the NAMES of the atomics a body reads and writes; an atomic is
ORDERED when declared `acquire`, `release` or `seq` (the emitter's table: loads acquire, stores
release, RMWs acq_rel, or seq_cst):

- **`N481`**: a take (`L_nimm`, `L_nimm_geteilt`) that reads atomics reads no ordered one;
- **`N482`**: a give (`L_gib`, `L_gib_geteilt`) that writes atomics writes no ordered one;
- **`N483`**: a bodied take and give of one lock, both ordered, share no ordered atomic that the
  give writes and the take reads — no synchronises-with edge.

| probe | expected | measured |
|---|---|---|
| `beispiele/gift/1201` relaxed test-and-set spinlock | `N481` (and `N482`) | `N042` ×2, `N481`, `N482`; `N323` silent |
| `beispiele/gift/1202` acquiring take, give through a relaxed second word | `N482` | `N042` ×2, `N482` |
| `beispiele/gift/1203` take acquires `HALTER`, give releases `ZURUECK` | `N483` | `N042` ×2, `N483` |
| snippet `geordneter_spinlock_besteht` (acquire word) | silent | `N323`/`N481`–`N483` silent |
| snippet `ticket_sperre_besteht` (`laufzeit/sperre.gab` shape beside `lock TOR`) | silent; relaxed `NOW` → `N481`+`N482` | as expected |
| snippet `entspannter_spinlock_faellt_mit_n481_und_n482` (relaxed / no word / `seq` / `release`) | fall / fall / silent / silent | as expected |
| snippet `zwei_worte_faellt_mit_n483` | `N483` only | as expected |
| corpus diff (921 files under `beispiele/`, `beispiele/gift/`) | only the new gifts | only 1201–1203 draw `N481`–`N483` |

**Finding (measured): `N042` refuses the C name of EVERY own or foreign `L_nimm`/`L_gib` beside
`lock L`** (also on the acquire spinlock and the ticket shape). So no accepted program has a
non-driver lock primitive today, and the old assumption (3) for own/foreign primitives was about
programs the checker already refused. `N481`–`N483` are the order half of the contract for the
day that name opens (e.g. the runtime's own ticket lock). Written into the sentence, OFFEN O26
and the Spec header.

**Alignment with the Lean condition for atomics (measured).** The Rust footprint legs
`N290`–`N294` never count atomics as carriers (`fusswache2.rs::bestand`: tables, statics, state),
so on this component the Rust checker decides `fussWAB` — `AkzeptiertA` — not the goal checker's
`fussWB`. `messung/proben/o25-flagge-atomar.gab` (a setter and a reader of one atomic flag, two
starts, no lock): Rust 0 errors; the exporter refuses it (`LG001`: no `atomic` has a G form). So
this gap between the checkers is on the Lean side (the goal is stricter), and the differential
test cannot see it, since no unit with an atomic exports.

## 6. What remains (named in OFFEN O25, TODO §2)

1. **The rely and the replay** — the contract legs over GA. `execEndH` must answer a read of a
   shared atomic with any value of its type. That is a havoc at the read, beside the one `Umwelt`
   makes at a lock take. `KoerperGutS` and `InvGutS` must hold over it, and every residue lemma
   of the replay (`ZielOrt*`, `Sperre*`, `ziel_ort_mehrfaden_ende` and around) must carry it,
   syncing the sequential world to the machine's presented atomic value the way the lock havoc
   is synced at a take. The memory premise it needs is `schwach_ist_gA`. Multi-lane, Opus-sized.
2. **Then ONE reviewed `Spec.lean` diff** (§4, items 1–4).
3. **RMW atomicity in W** (`zaehler_verloren`): the adjacency of `ZSchritt` in `SchrittW` for a
   step that reads and writes one atomic. The result is a smaller W, so every claim over W stays;
   `w_aus_g` needs re-checking (SC writes at `T+1` are adjacent to the newest message at `T`, so
   it should go through).
4. **A footprint rule for a plain payload read after an `awaits`.** The view transfer is proved
   (`hb_uebergabe`); the flow facts are not.
5. **The exporter for `atomic` items** (`LG001`).
6. **Foreign lock primitives** stay a named assumption. So does the lowering of the orders
   (assumption (2)).

Reserved numbers: `N484`, `N485` and gifts 1204–1210 are unused and stay with this wall (booked
in AGENTS.md §7).

## 7. Measurements

| run | result |
|---|---|
| `./lean-bau` (final, after the Spec header comment) | exit 0, 0 error lines, 297 jobs; `free -g`: 31 total, 19 available |
| `#print axioms gabbro_ziel` (`NachpruefungZiel.lean` via `./lean-probe`) | `[propext, Classical.choice, Quot.sound]` |
| `#print axioms` of every new theorem | the same three or fewer (`propext` alone for the decided Bools) |
| `sorry`/`admit`/`axiom`/`native_decide` in the three new files | none (grep: one hit, the word "admits" in a comment) |
| `./cargo-pruef` (1st run, before the English test messages) | 1331 passed, 1 failed: `bausystem::inkrementell_nach_inhalt_und_nicht_nach_zeitstempel` (a build-system test on `programmlogik/beispiel/lager.gab`, no relation to this branch) |
| `./cargo-pruef` (final, on the committed Rust) | exit 0, **1332 passed, 0 failed**, 1 ignored (the `bausystem` test of the first run passed: not this branch) |
| `pruefe-akzeptiert-diff.py` | `compared=22 skip=192 partial=2 findings=0 not-measured=0`, every component `true` on 20/20 |
| `pruefe-akzeptiert-diff.py --selbsttest` | ok, both directions |
| `pruefe-saetze.py` | exit 0, 446 codes, 186 sentences, 55 without (ratchet unchanged) |
| `pruefe-kennungen.py` | ALL PASS |
| `pruefe-englisch.py` | red, identical to the baseline `9ed1b5d7` (three ratchets broken there already; this branch adds nothing, measured by swapping the two Rust files back) |
| `pruefe-todo.py` | red, 16 findings, all stale counts (EBNF, bold numbers, Kennzahlen) this branch does not touch |
