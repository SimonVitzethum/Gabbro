# Language gaps against the Lean model (Lane 1397, second run)

Date: 2026-10-06. Author: muse-agent-1397.
Scope: what CANNOT be written in the current Gabbro language, measured against the
Lean model (`grammatik/`). Excluded by task: unbounded dynamic data structures (decided,
OFFEN O29; bounded arenas with a ceiling are in scope per TODO §0e).
Baseline: `messung/SPRACHLUECKEN-REPORT.md` (lane 1395, 12 ranked rows), reviewed row by
row in §3 below.

Method note: this lane ran with no shell execution (the session permission classifier
rejects `awk`/`sort`/`python3`/`cargo`/build-wrapper calls; only `git rev-parse`/`git
status` and file reads/searches succeed). Counts below were tallied by reading
`REGISTER.txt` in full (248 lines) and cross-checked per code with content search:
CERTIFIED 30, LG002 44, LG003 12, LG004 16, LG005 6, LG006 2, LG007 0, hence
LG001 = 194 − 80 = 114; total 224 accepted. Every row is therefore **measured**
(register text or a cited Lean/Rust source line), except rows marked **assessed**.
Re-measure with a shell when available:

```
awk -F'\t' '/^UNCERTIFIED/{print $3}' grammatik/Grammatik/Zertifikat/REGISTER.txt \
  | sort | uniq -c | sort -rn
awk -F'\t' '/^UNCERTIFIED\t.*\tLG001/{print $4}' grammatik/Grammatik/Zertifikat/REGISTER.txt \
  | awk '{print $1, $2}' | sort | uniq -c | sort -rn
```

Population: `REGISTER.txt` header — 224 accepted, 30 CERTIFIED, 194 UNCERTIFIED.
(OFFEN O27 recorded 176 on 2026-09-26; the register at this commit says 194. The drift
is corpus growth, not a contradiction, but O27's number is stale.)

Class key: LANGUAGE (cannot be said in the language or the model) · CERTIFICATION
(checker accepts and emits, the Lean exporter refuses: the program runs, no Lean
judgement) · GUARANTEE (refused although true, by a named open premise) · CEREMONY /
COMPUTE / RAM / PROOF-TIME / UGLY (part B only).

## 1. Histogram by exporter code

Meaning of each code: `crates/gabbro-check/src/lean_g.rs` header §"Refusal codes (`LG`)",
lines 172–196.

| code | n | exporter meaning | example programs |
|---|---|---|---|
| LG001 | 114 | item with no G form | devices (`12-umlaufendes-register`), marks (`04-schleifen`), formats (`03-format`), tables (`42-zaehlwerk`), klon/stack handoff (`155-kind-uebergabe`), `accumulates` (`05-nebenlaeufigkeit`) |
| LG002 | 44 | type with no `Ty` form | record value (`21-verbundwert`), array/pointer/record statics (`08-bereiche`, `150-fd-lesen`), float alias (`26-gleitkomma`), byte-pointer target (`168-bytes-through-a-pointer`) |
| LG003 | 12 | contract/value expression with no `Expr` form | gate `requires` (`74-syscall-schreiben`, `90-syscall-errno`), gate `ensures` (`183-region-vom-tor`), call in value position (`131-derived-contract-call`) |
| LG004 | 16 | body statement with no `Stmt`/`Endblock` form | top-level `alloc` (`98-arena-erklaert`, `153-arena-waechst`), top-level tail-let (`110-fussgarantie`), falls-off-with-result (`147-ftp-alg-control`), payload publish (`14-paarung-ueber-zwischenfunktion`) |
| LG005 | 6 | unresolvable name/count/rank/range | non-numeral const (`92-const-squares`, `123-const-matrix`), `grow` (`158-arena-commit`), unknown names (`19-traversierung`, `46-verneinung`) |
| LG006 | 2 | loop with no export form | `retry` fragment (`gift/166`), non-table `traverse` domain (`gift/435`) |
| LG007 | 0 | reason-channel form | (no corpus row) |

## 2. Histogram by message class (first words)

LG001 (114): linear/resource marks 13 (`02-geraet`, `04-schleifen`, `07-eintritt-und-boot`,
`09-ohne-zeiger`, `22-bootstrecke`, `39-auftragsdienst`, `54-divergenz-leckt-nicht`,
`58-freiliste-zwei-formen`, `66-transport-rueckgabe`, `114-owner-with-producer`,
`115-owner-read-with-producer`, `1001-eigentumsmarke-am-zeiger`, `halde`); devices
(`D.Reg`) 17 (`112`, `113`, `12`, `20`, `41`, `44`, `45`, `65`, `215`, `294`, `416`,
`653`–`657`, `672`); formats 11 (`03`, `133`, `24`, `51`, `197`, `291`, `292`, `446`,
`641`, `644`, `667`); tables carrying an unbuilt form 13 (`18`, `42`, `43`, `47`, `53`,
`55`, `196`, `286`, `333`, `434`, `441`, `442`, `689`); function `is not impl` 21 (mostly
intentional bodiless stubs — see M13: `106`, `107`, `11a`, `134`, `173`, `48`, `50`,
`60`, `63`, `68`, `70`, `72`, `80`, `94`, `95`, `1052`, `1053`, `1066`, `580`, `642`,
`658`); function carrying an unbuilt form 6 (`36`, `67`, `71`, `727`, `758`, `777`);
klon/stack handoff 6 (`1114`, `155`, `156`, `160`, `1181`, `1389`); `accumulates` 2
(`05`, `23`); placement statics (`section`/`aligned`) 6 (`40`, `175`, `646`, `663`,
`664`, `665`); `use`/unit boundary 2 (`29`, `167`); `requires profile` 2 (`100`,
`101`); unbuilt effect 2 (`35`, `117`); shared-hold locks 3 (`10`, `13`, `718`);
non-`syscall` foreign bodies (`axiom`/`entrust`) 2 (`06`, `25`); `group` 1 (`17`);
`when` 1 (`52`); `backed` 1 (`28`); writes-clause naming a value 1 (`gift/04`);
atomic payload 1 (`11`); `entry fn` code value 1 (`184`); `locks` neither held nor
taken 1 (`146`); table-less declaration 1 (`gift/666`). Sum: 114.

LG002 (44): statics with no `Glob` form 11 (`08`, `122`, `150`, `152`, `172`, `180`,
`38`, `64`, `96`, `602`, `645`); record-typed slot fields 10 (`111`, `126`, `127`,
`32`, `49`, `56`, `605`, `919`, `957`, `958`); fields with no integer-range/bool/tagged
form 4 (`27`, `31`, `33`, `195`); wrapping fields 3 (`01`, `159`, `37`); parameter
types 5 (`1123`, `1124`, `1126`, `1159`, `1166`); address spaces 4 (`132`, `415`,
`764`, `765`); pointer targets 2 (`168`, `169`); atomic globals 2 (`140`, `141`);
record-valued results 2 (`21`, `161`); float alias 1 (`26`). Sum: 44.

LG003 (12): gate `requires` 5 (`149`, `163`, `164`, `74`, `90`); gate `ensures` 2
(`183`, `1383`); call in value position 1 (`131`); `let…else` expression 2 (`1127`,
`170`); ensures-clause with no form 1 (`57`); `q->wert` past a pointer 1 (`1000`).
Sum: 12.

LG004 (16): top-level `alloc` 4 (`98`, `99`, `153`, `154`); top-level tail-let 1
(`110`); falls-off-with-result 3 (`125`, `147`, `148`); payload publish 1 (`14`);
index with no form 1 (`151`); `narrow` fragment 1 (`171`); `let` exceeding its
annotation 1 (`61`); `exchange` fragment 1 (`194`); unguarded global reads 3 (`916`,
`918`, `930`). Sum: 16.

LG005 (6): non-numeral const 3 (`92`, `123`, `445`); `grow` 1 (`158`); unknown names 2
(`19`, `46`). LG006 (2): `retry` fragment 1 (`166`); `traverse` domain 1 (`435`).

## 3. Baseline review: the 12 rows of lane 1395, against the model

Verdict per row: CONFIRM (with the Lean evidence the baseline lacked), CORRECT (it
needs a fix), or REFUTE. Nothing is fully refuted; three rows need correction.

1. **No generics — CONFIRM (LANGUAGE).** `Typen.lean` lines 35–59: `Ty` is a closed
   non-recursive inductive (`int | bool | opt | sum | grund | never | fl | fnptr |
   ptr`) with no parameter, application, or variable former; `Syntax.lean` has no type
   application either. Checker: `Queue<T>` unparseable (`P001`), `(T)` parses as the
   ghost-parameter list, not a parameter. Cheapest fix keeping every guarantee: the
   generator-with-byte-identity-guardian option of TODO §0b (no model change); a real
   parameter touches deliberately non-recursive `Ty` (O15's rule applies by analogy).
2. **Record as value — CONFIRM with refinement (LANGUAGE + CERTIFICATION).** Model wall:
   no `Ty.prod` (`Typen.lean` §1, quoted in register line 118). Second wall the baseline
   underplays: the C side has no aggregate either (`CTy := int | ptr`, `CVal := int |
   ptr | undef`, OFFEN O16) — a product former would add a second G form with the same
   unbuilt C side. Priced AND refused with zero gain (O15: sieve (b) stays 15 of 113;
   `21-verbundwert` has four walls, the last two being the `Endblock`-binder wall of
   row 9). Workaround stands: out-pointer or split results.
3. **`traverse` has no label — CONFIRM (LANGUAGE).** `Endblock.leave/next` take only
   `(h : l = true)` (`Syntax.lean` lines 605–606): the flag exists for `retry`/`forever`
   loops; a `traverse` binds no label, so `leave i` is S001 and `traverse runde i` is
   P001. Workaround stands: full guarded walk or hand-threaded `retry`.
4. **No windowed traverse — CONFIRM, still assessed (LANGUAGE).** No new model evidence
   either way; grammar has no window arms, TODO wave-B residue stands. Reaching for the
   Lean `traverse` form (`lean_g.rs` LG006: only `traverse i over slots of T` with a
   translatable invariant exports) shows even the unwindowed form is barely carried.
5. **`option` index-only — CONFIRM (LANGUAGE).** `Ty.opt (n : Int)` takes only the bound
   (`Typen.lean` line 40: "`option index into T`"); no former takes an ordinary type.
   `option u32` is unparseable. Workaround stands: hand-written `tagged` sum per type.
6. **`count` as predicate — CONFIRM (LANGUAGE, by design).** `let n = count …` checks
   (`beispiele/71`); the same shape in `invariant`/`spec fn` is D021. The model-side
   reason is visible in `Spec.lean` NOT CLAIMED: cross-carrier predicates are refused
   (`InvTraeger`), and cross-table count is refused by design (group invariant instead).
7. **Strings in aggregates — CONFIRM with correction (LANGUAGE, deliberate cut).**
   Representation landed: `gabbro_string_N` is `uint32_t len` + `uint8_t data[N]`, max
   `1 ..= 65535` (`saetze.rs` "zeichenfolge.laengen"; `zeichenfolge.rs`
   `MAX_OBERGRENZE = 65535`); `N465` still refuses aggregate positions. Correction to
   the baseline: the "max-bound over-approximation" refusal is sound-but-incomplete by
   construction (length-flow facts cannot reach the cut positions), not a separate bug.
   Register rows: `161` (LG002 result), `32` (LG002 field).
8. **Byte pointers / region answers — CONFIRM, updated (LANGUAGE + CERTIFICATION).**
   Register now says it precisely: `183` is LG003 (gate `ensures`: "`AxEns` reads the
   world and the answer, not the arguments; this exporter writes `Q := fun _ _ _ =>
   true`"), `168`/`169` are LG002 (pointer target), six klon rows are LG001
   (`Ax := Empty` over a `Deklaration` with no `klon` field). OFFEN O37: byte pointers
   have no G form, nothing releases a region. Programs run uncertified; no certifying
   workaround exists.
9. **`Endblock` binders — CONFIRM, highest leverage, with one correction (LANGUAGE).**
   `Endblock` (`Syntax.lean` lines 602–627) has `bind`, `bindAxiom`, `bindAxiomElse`
   but NO `bindCall`; `Block` (lines 537–546) has `bindCall`/`bindCallElse`. So every
   top-level tail-let of a call and every `alloc` at body top level is refused (LG004:
   `110`, `98`, `99`, `153`, `154`, plus falls-off `125`/`147`/`148`). Correction: the
   arena half is NOT a missing model form — `Block.arenaAlloc` exists
   (`Bausteine/Arena/ArenaZucker.lean` line 203; dynamic twin `Block.dynAlloc`,
   `ArenaDyn.lean` line 363, with proved simulation `dynAlloc_simuliert`); the wall is
   purely the missing `Endblock` rest. O15 measured this as what pays first
   (`21`/`98`/`99` plus every top-level tail-let). Re-rank: this row should be FIRST,
   ahead of row 2.
10. **`bool` static — CONFIRM with correction (emitter-side, not model).** The model HAS
    both halves (`Ty.bool`, `Typen.lean` line 38; `Glob` carries "an integer range,
    `bool` or a `tagged` type" per the LG002 message): checker-clean but C001 at emit.
    Correction: this is not a model gap at all — the cheapest fix is an emitter
    lowering, no Lean change. Workaround (`u32` flag) stands; cost is one word, trivial
    but paid by every boolean piece of shared state.
11. **Payload hand-off — CONFIRM (GUARANTEE-by-design, open rely).** Unchanged: the rely
    IS the goal (`PrueferX`/`NutzerPflichtA`/`ZielFX` over GX); the plain-payload rule
    needs happens-before race freedom plus flow facts and is not built (O25c; `N485`
    and gifts 1205–1210 still unused). Register rows `11` (LG001 atomic payload) and
    `14` (LG004 payload publish). Lock-guarded workaround keeps the guarantee.
12. **256-way dispatch — CONFIRM as cost, not expressiveness (COMPUTE/CEREMONY).** Arms
    cap at 256 values each (full-`u32` dispatch narrows first); writable as a comparison
    chain (1797-ops shape), just expensive at run time. G07 flow-precision cost only.

Re-ranking after Lean evidence: 9 (unblocks `21`/`98`/`99` + every tail-let; O15's
pays-first) → 2 (= 16, priced/refused pair) → 1 (whole library classes) → 8 (runs but
never certifies) → 3/4 (every table search) → 5/6/7 (concrete F5/F6/driver shapes) →
11 (open rely) → 10/12 (per-site costs). The baseline order is otherwise kept.

## 4. What the baseline missed (register-measured)

M1. **Floats emit but never certify (CERTIFICATION).** The model HAS the whole form:
`Ty.fl` with fractional bounds (`Typen.lean` line 49), `Block.gleit/gleitLit/gleitVon/
gleitNarrow` (`Syntax.lean` lines 590–600), kernel IEEE model (GLEITKOMMA §7, `Spec.lean`
NOT CLAIMED "floats only as the kernel IEEE model"). Checker accepts, emitter emits,
exporter refuses: `26-gleitkomma` is LG002 ("this exporter builds no `Ty.fl` and none
of the `Block.gleit*` statements"). Cheapest fix: build the existing form in the
exporter (no statement change). One corpus program pays it today.
M2. **Devices/registers: the largest LG001 class, 17 rows (CERTIFICATION).** The model
names the form (`D.Reg` with `rtyp`/`rklasse`/`spiegel`/`rzusage`,
`Block.regLies`/`Stmt.regSchreib` — register messages, e.g. `12-umlaufendes-register`);
the exporter builds no `Reg` (`lean_g.rs` LG001 class (i) is "built nowhere" only for
the linear family; devices simply have no builder). Every MMIO program runs but never
certifies. Cheapest fix: exporter `Reg` construction; the C side (`volatile uint64_t`
accesses, `namen.rs` device lowering) already exists.
M3. **Linear/resource marks, 13 rows (CERTIFICATION, priced, zero measured gain).**
The specification HAS all of it (`D.Marke`, `D.stufen`, `konsumiert`/`produziert`,
`Stmt.advances/retires` — `lean_g.rs` lines 154–162); the exporter writes
`Marke := Empty` and refuses by name. Measured 2026-09-15 (`lean_g.rs` lines 164–170):
the ten corpus programs at this wall each stop at a SECOND wall from another group,
so closing the family moves sieve (b) by zero. Keep refused until the second walls
fall; the register rows are `02`, `04`, `07`, `09`, `22`, `39`, `54`, `58`, `66`,
`114`, `115`, `1001`, `halde`.
M4. **Formats, 11 rows (CERTIFICATION).** Model form named (`Tab` with `count 1`,
`where` clauses as `Block.pruefung` — register messages, `Syntax.lean` §9); exporter
builds no such table. Examples `03-format`, `24-ip-kopf`, `51-abwesenheit-und-absage`.
M5. **`accumulates`, 2 rows (CERTIFICATION).** A `Glob` plus a generated assignment
(`Syntax.lean` §11); the exporter generates none (`05-nebenlaeufigkeit`,
`23-akkumulatoren`; OFFEN O17: "Open: the exporter for `accumulates`").
M6. **Gate contracts, 7 rows (CERTIFICATION).** `D.Ax` carries no precondition and
`AxEns` reads world+answer, so any `syscall` gate with `requires`/`ensures` is refused
(`74`, `90`, `149`, `163`, `164`, `183`, `1383`). The two oldest syscall programs in
the corpus (`74-syscall-schreiben`, `90-syscall-errno`) run but never certify for this
reason alone. Fixing needs a statement move (duties nobody states today), not just an
exporter arm — genuinely harder than M1/M2/M4/M5.
M7. **Code values, 1 row (LANGUAGE).** `184-code-vom-treiber`: "takes `lauf`, an `entry
fn` — code a generated driver hands in, and G has no code values" (LG001; checker
N575–N577, gifts 1394–1397). No workaround inside the language; the callback shape
stays uncertified.
M8. **Group invariants, 1 row (CERTIFICATION).** `17-gruppe-ueber-zwei-sperren`: a
`group` is a `D.Inv` over more than one carrier (`Syntax.lean` §11); the exporter
writes `Inv := Empty`. Single-carrier invariants of the same program would certify;
the cross-carrier one cannot.
M9. **Unit boundary, 2 rows (LANGUAGE, half-covered).** `29`, `167`: "`use` names
another UNIT, and `Deklaration` has no unit boundary". Half-covered since Opus agent E
by the second statement `GabbroZielVerbund` (two units, one link declaration,
`Spec.lean` linking hunk) — but the single-term exporter still refuses the importing
unit alone, so each importing program is uncertified as a unit.
M10. **Non-numeral consts, 3 rows (CERTIFICATION, small).** `92` (SQUARES), `123` (T),
`445` (H): the exporter inlines numeral consts only (LG005). An array-valued const is
accepted by the checker and has no path to `Einheit`. Small, self-contained exporter
work.
M11. **Placement statics, 6 rows (CERTIFICATION).** `section`/`aligned` are PLACEMENTS
with no `Glob` form (`40`, `175`, `646`, `663`–`665`). `175-puffer-gibt-seiten-zurueck`
(the page-return program, RSS-measured) runs but stays uncertified for the placement
word alone.
M12. **Shared-hold locks, 3 rows (LANGUAGE).** `10`, `13`, `718`: a shared hold "with
no G counterpart" (exporter header line 98: the `shared held <= …` branch still has no
G form). Exclusive-hold twins certify (`719-lock-taken-nowhere` is CERTIFIED).
M13. **"Function is not `impl", 21 rows (MIXED — mostly by design, assessed).** Most
are intentional bodiless declarations the corpus keeps as probes or tutorial stubs
(`106`/`107` summe-uebersetzt, `63` putchar, `80`/`94`/`95` uebersetzer, `60`, `70`,
`72`, `173`): nothing is missing from the language — a body was never written. Do NOT
count all 21 as gaps. The genuine residue inside this class: `buchfuehrung_kaputt`
(`48`), `ist_frei` (`50`), `liest` (`68`), whose callers want them; and the tutorial
chain behind `80`/`94`/`95` (see O16: stopped two sieves earlier at (b) by this).
M14. **Long tail, one line each (all register-measured).** Falls-off-with-result
(`125`, `147`, `148` — CERTIFICATION, `Endblock` return-position restriction);
`61` let-exceeds-annotation, `171` narrow-fragment, `194` exchange-fragment, `151`
index-form (CERTIFICATION, fragment shapes the exporter never built); `131`
call-in-value-position, `1127`/`170` let…else-expression, `57` ensures-clause
(CERTIFICATION, `ErgExpr` coverage); `132`/`415`/`764`/`765` address spaces,
`140`/`141` atomic arrays, `1000` arrow-past-pointer (CERTIFICATION, `Ty`/carrier
coverage); `01`/`37`/`159` wrapping fields, `161` string result, `27`/`31`/`33`/`195`
non-scalar fields (CERTIFICATION, one-`Ty`-per-field rule); `158` `grow`
(CERTIFICATION, exporter builds the static `ArenaForm` of `hi`, not the committed
prefix — `Spec.lean` lines 1441–1447 say exactly this); `19`/`46` unknown names
(LG005, exporter resolution, not language); `146` locks-neither-held-nor-taken,
`666` table-less declaration, `04` writes-clause-naming-a-value (LG001 item rules);
`100`/`101` hardware profiles (NAMED ASSUMPTIONS the declaration only carries as
`D.Annahme` — model-covered elsewhere, exporter-unbuilt); `35`/`117` unbuilt effects;
`52` `when`; `28` `backed`; `06`/`25` non-`syscall` foreign bodies (exporter builds
`Ax` only for `syscall` gates); `36` asm; `67`/`71` unbuilt function forms. No
assessment beyond the register message in any of these rows.

Deliberately NOT listed as gaps (no change from baseline): unbounded heaps (out of
scope); `tagged` construction, pointer indexing, `narrow` scope, `let…else`
annotation, cross-unit access, worker pools, per-core accumulator write half (all
closed, see baseline §"Expressly not gaps"); the 21 `not impl` stubs as a class (M13).

---

# PART B — Cost and ceremony: what is inefficient, ugly, or very laborious

Same scope rule (unbounded dynamic structures excluded), same evidence rule (measured
from a cited source, else marked assessed / not measured). Run-time cost and
check/proof-time cost are never mixed: each row names which clock it bills.

## RAM (emitted-binary memory)

- **R1. Strings pay `4 + max` bytes for every value.** Layout `gabbro_string_N`:
  `uint32_t len` plus `uint8_t data[N]` (`saetze.rs` "zeichenfolge.laengen": "here
  lowers since lane 261 … `uint32_t len` plus `uint8_t …`"; cap `1 ..= 65535`,
  `zeichenfolge.rs` `MAX_OBERGRENZE = 65535`). A 5-byte greeting with `max 100` costs
  104 bytes; the cap forbids anything past 65535 by lowering decision, not by model.
  Class RAM. Measured in code (layout), per-program bytes not measured. Cheapest
  guarantee-keeping improvement: none needed for most programs — declare a tight `max`
  (already expressible); the 4-byte word itself is the lowering's, and shrinking it
  (e.g. `uint16_t` for small maxima) is emitter work with no statement change.
  Payers: string programs (`32-zeichenkette`, `161-zeichenkette` — both uncertified
  for other reasons, M14/row 7).
- **R2. Tables and arrays are always fully sized.** Every slot array spans its declared
  `count`; every arena spans `hi` (the exporter builds "the static `ArenaForm` of `hi`
  slots" — register line 90; `Spec.lean` lines 1441–1447). No partial/live-prefix
  representation exists in the emitted C. Class RAM. Bytes not measured in this lane.
  Cheapest guarantee-keeping improvement: the bounded dynamic arena (ceiling `M`, in
  scope per §0e; model side DONE — `Block.dynAlloc` + `dynAlloc_simuliert`,
  `ArenaDyn.lean` — exporter `grow` LG005 pending, register line 90).
- **R3. The `u32`-for-`bool` flag idiom costs a word per flag.** Boolean statics check
  clean but do not emit (row 10 of §3); the workaround every service loop uses is a
  `u32` `0`/`1`. Class RAM (4 bytes vs 1, plus comparisons — trivial per site, paid by
  every boolean piece of shared state). Assessed (no corpus file holds the F5 loop;
  S15/S16 probes demonstrate the refusal). Cheapest fix: emitter lowering for
  constant-initialised `bool` statics (no model change — `Ty.bool` and `Glob`-bool
  both exist).
- **R4. Missing generics duplicate code per shape.** One ring/queue/copy per element
  type (§3 row 1; TODO §0b). Class RAM (.text) and COMPUTE (icache) — billed here once
  as RAM. Sizes not measured (no binary-size census exists). Cheapest fix: the
  generator-with-byte-identity-guardian of TODO §0b (no model change).

## COMPUTE (run time)

- **C1. Table search without exit costs a full walk per query** (§3 row 3). The
  workaround walks all N slots guarded by `if !gefunden` where C tests 1 (baseline:
  64 passes where C does 1). Class COMPUTE, run time, factor O(N) per search. Payers:
  every find-first over a table (firewall IPC fastpath, F1 `peak_revoke_ops`).
  Guarantee-keeping fix: a labelled `traverse` (grammar + `leave` former + exporter;
  no guarantee moves — the bound is already proved for the full walk).
- **C2. Dispatch over integers is a comparison chain** (§3 row 12). 256 values per arm
  max; full-`u32` dispatch narrows first; the firewall shape is 1797 ops. Class
  COMPUTE, run time. Guarantee-keeping fix: jump-table lowering in the emitter for
  dense arm sets (semantics unchanged; the C proof side would need the new emitted
  shape carried — translation-validation work, not a checker change).
- **C3. Bounds are re-proved per access.** Without windowed traversal (§3 row 4) every
  access carries its own `narrow`/bound check instead of one entry check; the same
  holds wherever a range must be re-established after restructuring around row 9.
  Class COMPUTE, run time. Fix rides with rows 4 and 9.
- **C4. Lock traffic on lock-free-designed paths** (§3 row 11). The payload hand-off
  that C does with release/acquire takes a lock in Gabbro (guarantee kept, not lost).
  Class COMPUTE, run time. Fix is the open O25c payload rule (needs happens-before
  race freedom + flow facts — proof work, no weakening).
- **C5. Check-time compute is NOT run time (labelled, not mixed).** `gabbro costs`
  fixpoint vs `pruefe` silence on the `33-rekursion` cycle trio (70 vs 64) is a
  check-time divergence, already recorded in SCHREIBLAST §3. No run-time claim.

## PROOF-TIME (checker, exporter, Lean — never run time)

- **P1. Duty proof bills 0.42 lines per code line — on a sample of four.**
  `messung/GABBROV-PROOF-RATIO.md`: 57 duty-proof lines over 136 code lines (0.42),
  spread 0.13 (`124-two-threads-private`) to 0.91 (`120-tagged-construction`).
  Class PROOF-TIME. The sample is small (4 units); treat 0.42 as a datum, not a rate.
  12 proof obligations owed (task citation — re-measure via `gabbro obligations`;
  O15 books 126 obligations over the 113-program corpus of 2026-09-15).
- **P2. Lean build and export coverage bound.** 30 of 224 accepted programs are
  CERTIFIED (13%); every other program's proof must be a hand-written term (register
  header; `Korpus07.lean`, `Korpus125.lean` exist for exactly two). The build-time
  cost of the model itself was not measured in this lane (no Lean slot access) and is
  recorded as not measured rather than estimated.
- **P3. Obligations scale with contracts, not code.** O15: `gabbro obligations` reads 1
  obligation on `21-verbundwert` (1 precondition, open) and 126 over the corpus.
  Class PROOF-TIME. Follows the contract surface (63 hand-written `ensures` sites per
  PLAN-EINFACHHEIT §2 — underivable by design, "a tool that guesses the postcondition
  guesses the specification").

## CEREMONY (text a correct program needs beyond its idea)

- **E1. Bookkeeping outnumbers logic 757 to 210.** `messung/SCHREIBLAST-EFFECTS.md`
  (71 files, 1125 sites): BOOKKEEPING T1+T2+T7+T8 = 757, OWN LOGIC = 210, HARDWARE =
  87, DERIVABLE = 71. Every one of the 71 corpus files pays it. Class CEREMONY.
  Cheapest guarantee-keeping cut (PLAN-EINFACHHEIT §1): derive `effects`/`costs`
  (about 767 of roughly 980 clause sites) with the enforced-bound reading — 316 of
  389 body effects (81%) are already consistent with what the bodies say
  (SCHREIBLAST §2: 281 RIGHT + 35 pure-empty), so an elaborator could write them;
  load-bearing are the 93 `extern`/`prim` entries (trust surface, can never fall) plus
  40 holes. `ensures` (63 sites) stays by hand — deriving it guesses the spec.
- **E2. The pass register is the floor.** 386 diagnostics say what to write
  (PLAN-EINFACHHEIT §1 lever 4: refusals that ship the fix, machine-applicable). The
  ceremony count falls only while the register stays constant — booked before and
  after each step. Class CEREMONY (the number that stops ceremony cuts from becoming
  guarantee cuts).
- **E3. Largest-files accounting: not measured in this lane.** The task asks for the
  largest corpus files by `requires`/`ensures`/`effects` lines against code lines; no
  shell means no fresh census, and SCHREIBLAST-EFFECTS.md aggregates by rule, not by
  file. Recorded as not measured, not guessed. Nearest existing datum: E1/E2 above.

## UGLY (spellings that surprise or mislead; two witnesses per idiom)

- **U1. `(T)` parses and means something else.** `type Queue(T) = …` parses with 0
  errors (the ghost-parameter list of `linear ghost type Held(Lock)`), `gabbro emit`
  is byte-identical to the unparameterised type, and using `T` dies at the emitter
  (`C001`); `Queue<T>` never parses (`P001`). Witnesses: `messung/schreibprobe/S20`
  header + any `linear ghost` declaration (e.g. the `1001`/`halde`/`58` shapes —
  `beispiele/58-freiliste-zwei-formen.gab`, `halde.gab`). Class UGLY (bordering
  LANGUAGE: the parse succeeds and the meaning is silently different). Cheapest fix:
  refuse `(T)` on a non-ghost type at parse/check time (a new refusal, no weakening).
- **U2. `leave` names a label most loops cannot take.** `leave i;` inside `traverse`
  is S001; only `retry`/`forever` take labels. Witnesses: `beispiele/19-traversierung.
  gab` + `messung/schreibprobe/S13` header (+ `SYNTAX.md:1247`). Class UGLY. Fix rides
  with C1.
- **U3. `option` that is not optional.** `option Sektoren` as a result is
  "`P001`: 'index' expected, identifier found" — the word promises ML-style option and
  delivers index-only. Witnesses: `messung/schreibprobe/S12` header + OFFEN O5 (F5
  `capacity : option Sectors`, F6 `frei_min : option Bytes` — both unwritable).
  Class UGLY. Fix: generalise or rename; renaming alone is honest only with the
  generalisation (a rename without the form trades one surprise for another).
- **U4. `u32` for a flag.** The service-loop stop flag is written `0`/`1` because
  `static mut anhalten : bool` checks but never emits (row 10). Witnesses: S15/S16
  probe headers (no corpus file holds the F5 loop — assessed as idiom, measured as
  refusal). Class UGLY. Fix rides with R3.
- **U5. Out-pointer instead of `return`ing the value.** `return Completion(id: k, len:
  n)` checks and emits but never certifies (row 2/O15); the working idiom threads an
  out-pointer. Witnesses: `beispiele/21-verbundwert.gab` (the attempt) +
  `beispiele/120-tagged-construction.gab` (emits `return (Nachricht){ … };` by value —
  the C the model cannot carry, O16). Class UGLY (the language's own value syntax is
  the uncertified one). Fix rides with rows 2/9.
- **U6. Hand-counted loop variables instead of `count`.** The invariant that should say
  `refcount_matches` is a comment next to a manual counter. Witnesses:
  `beispiele/19` line 67 + `beispiele/46` line 51 (via baseline; not re-read in this
  lane — cited, not re-measured). Class UGLY. Fix rides with row 6.

Ranking by payers: E1 (all 71 files) → C1 (every find-first) → E2/U5 (every record
return) → R1 (every string value) → C2 (every large dispatch) → U2/U3/U6 (concrete
driver shapes) → R3/U4 (one flag per service) → P1–P3 (proof authors only, never
mixed with run time).
