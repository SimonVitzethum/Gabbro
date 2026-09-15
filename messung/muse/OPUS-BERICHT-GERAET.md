# A chain for a program that touches a device

*Opus agent `geraet`, 2026-09-16. Branch off `master` 83b6481c.*

Gabbro exists for an operating system, and until today the honest sentence was: *the two
closed chains contain no device and no foreign call.* This report says what was measured,
what was carried, what the chain now claims, and what it refuses by name.

---

## 1. The measurement, first

### 1.1 Which corpus programs touch a device or an axiom

**The corpus is `beispiele/*.gab`, 113 tracked files** (`instrumente/korpus.py`: membership is
`git ls-files`, not a directory). `beispiele/gift/` (686), `messung/**` (215), `messungen/` (2)
and `programmlogik/beispiel/` (2) are *not* the corpus and are excluded below.

Counts are taken on **comment-stripped** text (Gabbro line comments are `--` to end of line;
a raw `grep -c` overcounts badly — `53-zwei-orte.gab` has three prose hits for
`transition` and no transition). Declaration patterns, Python `re`, `(?m)`:

| column | pattern |
|---|---|
| `device` | `^\s*device\s+\w+` |
| `reg` | `^\s*reg\s+\w+` |
| `transition` (decl) | `^\s*transition\s+\w+` |
| `axiom` | `^\s*axiom\s+\w+` |
| `awaits` | `\bawaits\s*\{` |
| `forever` | `^\s*forever\s+\w+` |

Register **accesses** are not greppable by a fixed string. The procedure: collect the declared
register names per file (`^\s*reg\s+(\w+)`), then over every statement line that is neither a
declaration nor a clause line (`effects|requires|ensures|touches|publishes`) match
`(?<![\w.])(\w+)\.(REGNAME)\b((?:\.\w+)?)` and classify by what follows: `=` (not `==`) is a
STORE, a compound `+= -= *= /= |= &= ^=` is a store **and** a read, anything else a read. A
`let x = <reg> else (e) { … }` line is then moved into the "with else" column
(`let\s+\w+\s*=\s*\w+\.REG.*\belse\s*\(`). Every count was cross-checked against a full read of
the thirteen register-bearing files.

| program (`beispiele/`) | reg decls | reads | reads w/ else | stores | transition decl/call | axiom decls | axiom calls | awaits | forever |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `02-geraet.gab` | 9 | 2 | 0 | 3 | 4 / 2 | 0 | 0 | 0 | 0 |
| `04-schleifen.gab` | 1 | 1 | 0 | 0 | 0 / 0 | 0 | 0 | 0 | 2 |
| `05-nebenlaeufigkeit.gab` | 0 | 0 | 0 | 0 | 0 / 0 | 0 | 0 | 1 | 0 |
| `06-annahmen.gab` | 0 | 0 | 0 | 0 | 0 / 0 | 4 | 0 | 0 | 0 |
| `07-eintritt-und-boot.gab` | 0 | 0 | 0 | 0 | 0 / 0 | 4 | 0 (4 `step`) | 0 | 0 |
| `09-ohne-zeiger.gab` | 3 | 1 | 0 | 1 | 2 / 2 | 0 | 0 | 0 | 0 |
| `11-grammatikbefunde.gab` | 0 | 0 | 0 | 0 | 0 / 0 | 1 | 0 | 0 | 0 |
| `112-register-traeger-bewacht.gab` | 1 | 1 | 0 | 0 | 0 / 0 | 0 | 0 | 0 | 0 |
| `113-register-traeger-ungeschrieben.gab` | 2 | 2 | 0 | 0 | 0 / 0 | 0 | 0 | 0 | 0 |
| `117-message-passing-flag.gab` | 0 | 0 | 0 | 0 | 0 / 0 | 0 | 0 | 1 | 0 |
| `12-umlaufendes-register.gab` | 2 | 1 | 0 | 1 | 0 / 0 | 0 | 0 | 0 | 0 |
| `14-paarung-ueber-zwischenfunktion.gab` | 0 | 0 | 0 | 0 | 0 / 0 | 0 | 0 | 1 | 0 |
| `20-falle-vier.gab` | 2 | 0 | 0 | 0 | 2 / 0 | 0 | 0 | 0 | 0 |
| `37-umlauf-rechnet.gab` | 1 | 2 | 0 | 1 | 0 / 0 | 0 | 0 | 0 | 0 |
| `39-auftragsdienst.gab` | 0 | 0 | 0 | 0 | 0 / 0 | 0 | 0 | 1 | 2 |
| `40-werte-und-griffe.gab` | 2 | 1 | 0 | 0 | 0 / 0 | 0 | 0 | 0 | 0 |
| `41-handschlag.gab` | 4 | 4 | 0 | 3 | 0 / 0 | 0 | 0 | 1 | 3 |
| `42-zaehlwerk.gab` | 0 | 0 | 0 | 0 | 0 / 0 | 0 | 0 | 5 | 1 |
| `43-gegenprobe.gab` | 0 | 0 | 0 | 0 | 0 / 0 | 0 | 0 | 1 | 0 |
| `44-register-einmal-lesen.gab` | 3 | 2 | **1** | 1 | 0 / 0 | 0 | 0 | 0 | 0 |
| `45-gemischte-registerklasse.gab` | 3 | 2 | 0 | 1 | 1 / 0 | 0 | 0 | 0 | 0 |
| `54-divergenz-leckt-nicht.gab` | 0 | 0 | 0 | 0 | 0 / 0 | 0 | 0 | 0 | 1 |
| `65-port-space.gab` | 3 | 3 | 0 | 3 | 1 / 0 | 0 | 0 | 0 | 0 |
| `70-kernel-namen.gab` | 0 | 0 | 0 | 0 | 0 / 0 | 0 | 0 | 0 | 1 |
| `96-buffered-writer.gab` | 0 | 0 | 0 | 0 | 0 / 0 | 0 | 0 | 0 | 1 |
| **25 of 113** | **36** | **22** | **1** | **14** | **10 / 4** | **9** | **0** | **11** | **11** |

Thirteen programs declare a `device` (eighteen devices; `02` and `44` have two each), one has a
`bank`, four have `mirrors`.

**Three numbers matter more than the rest.**

- **`axiom` calls in the whole corpus: ZERO.** Nine axioms are declared and none is called from
  an `impl fn` body. The four `step write_cr3(…)` lines of `07-eintritt-und-boot.gab` are
  boot-ladder entries, not `Stmt.axiomCall`. *A driver call over the ABI is not in the corpus at
  all* — so the axiom form could not have been closed against a corpus program today even if it
  were carried.
- **Register reads with `else`: exactly ONE**, `44-register-einmal-lesen.gab:103`
  (`let t = d.TIEFE else (e) { return Geraetelug::ZuTief; }`), against the only declaration with
  a `requires … else` clause (`44:89`).
- **`20-falle-vier.gab` declares registers and two `transition`s and contains no function at
  all** — a pure declaration program, hence no read and no store.

### 1.2 How far each gets through the five sieves today

**No register-bearing program reaches sieve (b).** Every one of the 25 above is among the 111
programs that stop at sieve (a) — the Lean parser and elaborator (T3). The chain count of record
is **2 of 113** (`beispiele/104-referenz.gab`, `beispiele/108-disjoint-start-locks.gab`), and
neither declares a `device`, a `reg`, an `axiom`, an `awaits` or a `forever`. The sieve totals of
record (`zaehle-kette.py --lean`, `messung/muse/OPUS-BERICHT-LINEAR.md`) are
**(a) 2, (b) 15, (c) 15, (d) 60, (e) 2**.

> `zaehle-kette.py` was **not** re-run for this report: it needs `target/debug/gabbro`, which this
> worktree does not have, and with `--lean` it builds. The chain-count line below is therefore a
> reading of the record plus a *reason*, not a fresh measurement — and the reason is that this
> lane touched sieve (e) only, while sieve (a) binds. **Chain count 2 of 113, unchanged, and it
> could not change.**

### 1.3 What each of the five hardware forms would need on the C side

`korrOk` refused exactly five syntactic forms because each can end a call in `Hardware`
(`RufOhneHardware.lean`). What each needs, measured against `emit.rs` and the T4 lemma stock:

| form | model outcome | emitted C | T4 lemma | what a row needs | state after this lane |
|---|---|---|---|---|---|
| `Stmt.regSchreib` (`R = e;`) | *none* — a write has no answer | `(*(volatile uint32_t *)(d->basis + 24)) = (uint32_t)x;` | `regSchreib_step` (H10) | an address the check can decide, the cell width, the value expression | **CARRIED** (`GRow.storeReg`) |
| `Block.regLies` (`let x = R;`) | `register` (answer outside the type), `geraet` (answer against the declared promise) | `uint32_t _s = (*(volatile uint32_t *)(d->basis + 28));` | `regLies_step` (H9) | the same, plus a fresh C local and its declared type | **CARRIED** (`GRow.loadReg`) |
| `Block.regLiesElse` (`let x = R else (c) { … }`) | `register` only — the promise is a BRANCH | the read, then `if (!(c)) { … }` | none before today | the read, the condition, and the `else` branch as rows | **CARRIED with the `else` narrowed to a `return`** (`GRow.loadRegElse`) |
| `Block.awaits` (`let x = A awaits {…}`) | `sichtbarkeit` (A10) | `T x = atomic_load_explicit(&A, o);` | `bsem_awaits` (H3) | an atomic row (`GRow` has none) and the payload | **REFUSED, by name** — §5 |
| `Stmt.axiomCall` / `Block.bindAxiom` | `annahme` | `f(a, b);` / `T x = f(a, b);` to a foreign symbol | `scorr_axiomCall` (H5), under the `AxCorr` assumption | a foreign-call row and the per-axiom `AxCorr` premise | **REFUSED, by name** — §5 |
| `Stmt.forever` | `fortschritt` (H2) | the watchdog line, then `for (;;) { … }` | `scorr_forever` (F1) | a loop row whose body may leave only through `goto` | **REFUSED, by name** — §5 |

### 1.4 The C-form census: the register rows were already NAMED ASSUMPTIONS

`instrumente/pruefe-cformen.py` knows three register-related C forms, and all three are in state
(ii) — a **named assumption**, neither a lemma nor uncovered:

| form id | declared | assumption row | state |
|---|---|---|---|
| `stmt:reg-store` | `pruefe-cformen.py:131` | `:265` — `["RegLokal"]` | assumption |
| `stmt:reg-load` | `:132` | `:259` — `["hdev", "RegLokal"]` | assumption |
| `expr:volatile` | `:184` | `:268` — `["hdev", "RegLokal"]` | assumption |

That is the honest status for a DEVICE and this lane does not change it: `RegLokal`
(`ZielOrtGeraetSem.lean:48`) bounds what a register answer may depend on, and `hdev`
(`CFormenH.lean:626`) links the C device oracle to Gabbro's. What this lane adds is the other
half — that the emitted C ACCESS corresponds to the model's register STEP — and that half is
now a theorem inside the certificate rather than a per-program lemma.

---

## 2. What was carried, and how

*(Filled in below; see §3 for the sentence the chain claims.)*

### 2.1 Three rows, and a device table that is plain data

`GRow` (Korrespondenz.lean) gained three constructors:

```lean
| storeReg    (cp : CX) (w : CWidth) (ce : CX)
| loadReg     (x : Nat) (tc : CTy) (cp : CX) (w : CWidth)
| loadRegElse (x : Nat) (tc : CTy) (cp : CX) (w : CWidth) (cc : CX) (cr : Option (CTy × CX))
```

elaborating to `CS.vstore`, `CS.set … (CX.vld …)` and the latter followed by
`if (!(c)) { return e; }`.

The check cannot read off a row WHICH register it is — that is the emitter's layout, not the
program text. So `korrOk` gained a last parameter, **`GT : GerTafel D`**, a structure of plain
data with **no proof field** and a default of the EMPTY table (`ein := false`). Under the empty
table every device row is refused, and the two closed chains pass no `GT` at all: their call
`korrOk EL fnum c P fs` is unchanged, character for character, and so is what it decides.

### 2.2 One named premise: `GerAnnahme`

Everything a device row needs that a certificate cannot decide is collected in ONE structure,
`GerAnnahme EL orc O GT`, and every field is conditional on `GT.ein = true`:

| field | says | status |
|---|---|---|
| `fenster` | the register sits at its offset in a block the layout declares `mmio`, in a cell of the declared width, and that block is one `EmitLay.devs` names | layout fact |
| `adr` | every address expression the check ACCEPTS evaluates to the register's cell, in every state and frame, touching neither memory nor the trace | **theorem** for the direct-base spelling (`gerAdr_devH`, out of `ev_devReg`); **assumption** for the emitter's handle spelling `d->basis + K` |
| `passt` | the register's declared Gabbro type fits the cell | layout fact |
| `einig` | the C device oracle and Gabbro's `Orakel.regLies` answer the same machine | **the named assumption** — `regLies_step`'s `hdev`, lifted from one program point to the unit |
| `rund` | where the raw word DOES fit the declared type, its decoding encodes back to it | **theorem** for an integer register (`gerRund_int`); a `bool` register cannot meet it, and that is a refusal by name |

`gerAnn_leer` proves the empty table meets the profile vacuously — which is why the generic
theorem lost NO hypothesis it had before.

### 2.3 The one line that is not in the certificate: the window must be MAPPED

`corrW` — the state relation every judgement of pass (i) carries — relates the C **memory** to
the Gabbro world. A device window is not memory, and `CFormenH.lean`'s own CUT says so:
*"device windows are not in the relation … carrying device liveness through `StmtCorr` would put
it into every judgement."*

**That is exactly what was done, and it is the honest place for it.** `EmitLay` gained a field
`devs : Nat → Bool := fun _ => false` — the device windows the emitted unit declares — and
`corrW` a third clause:

```lean
(∀ d, EL.devs d = true → st.live (.dev d) = true)
```

*The alternative was a premise of the form `∀ σ st, corrW EL σ st → st.live (.dev d) = true`,
and that premise is FALSE whenever `D.Reg` is inhabited* — take any related state and flip the
device's liveness; `corrW` still holds. A theorem under a false premise is not a weak theorem,
it is no theorem, and this one was written, read back and thrown away before it was committed.
With the clause in the relation, the mapping is a PREMISE the reader meets at the top of the
chain (`hw : corrW EL σ st` in `korrOk_jeder_lauf`), it is preserved by every lemma that
preserves `corrW` (none of them touches `live`), and the default `devs = fun _ => false` leaves
the relation of before unchanged, character for character.

Cost, measured: **corrW has 300 occurrences in `grammatik/`, and exactly 17 of them had to
move** — the destructurings `h.2 g hgg → h.2.1 g hgg` and the constructions that now carry a
third component.

### 2.4 The three step judgements

- `gerSchreib_step` — a `StmtCorr` for `Stmt.regSchreib` at ANY accepted address. A device write
  has no Gabbro trace (`Orakel.regSchreib` answers `Unit`), so what is proved is that the C
  statement RUNS, changes no memory, and leaves the relation standing; the observation it
  appends has no model half to compare it to. *That absence is the store side of the named
  assumption, and it is written into the docstring, not left to be noticed.*
- `bsem_regLies` — a `BlockSem` for `Block.regLies`. Two of the model's five hardware outcomes
  live here and NEITHER is discharged: an answer outside the declared type is
  `Hardware.register`, an answer against the declared promise is `Hardware.geraet`, and in both
  the Gabbro block ends in an error, where `BlockSem` claims nothing.
- `bsem_regLiesElse` — a `BlockSem` for `Block.regLiesElse`, **the interesting one**. A device
  promise that does not hold is a BRANCH of the program, not a stop: `Hardware.geraet` is gone,
  and the `else` arm must correspond like any other. What is left is the ONE outcome no program
  can catch — an answer outside the declared TYPE, where there is no value to branch on.

---

## 3. What the chain claims, and what it does not

> **If the profile holds and the register answers inside its declared type, every run of the
> emitted C corresponds.**

Written out, for a certified unit with a device table `GT`:

- **PREMISES, all visible in the theorem:** the certificate checks (`korrOk … GT = true`, a
  Bool); the hardware profile holds (`GerAnnahme EL orc O GT` — the window, the address, the
  declared type, the two oracles, the read-back); the C state is related to the Gabbro world
  (`corrW EL σ st`), which since this lane INCLUDES that the unit's device windows are mapped;
  the C arguments are related to the Gabbro ones; and the Gabbro call ends in no model error.
- **CONCLUSION:** the C call has a run, and — the C semantics being deterministic — EVERY run of
  it ends in a state related to the Gabbro outcome.

**What it does NOT claim, by name.**

1. **Nothing about what the device does.** Not that it answers, not that it answers the truth,
   not that it keeps the promise its declaration states. Where the answer does not fit the
   declared type (`Hardware.register`) or breaks the declared promise (`Hardware.geraet`), the
   Gabbro side ends in an error and the correspondence says nothing at all.
2. **A device write has no model half.** `Orakel.regSchreib` answers `Unit`; the `.vwr`
   observation the C appends is related to no Gabbro trace.
3. **The two oracles being one machine is assumed** (`GerAnnahme.einig`), not proved. It is
   `regLies_step`'s `hdev` and `pruefe-cformen.py`'s `stmt:reg-load` row, in the theorem's
   premise list where a reader meets it.
4. **The device window being mapped is assumed** — now as a clause of the state relation, and so
   as a premise of every chain instance that names a device.
5. **The emitter's own address spelling is assumed.** `emit.rs`'s `geraetelesung` writes
   `(*(volatile uint32_t *)(d->basis + 24))` — through a handle struct — while `ev_devReg` models
   the direct-base spelling `(volatile uint8_t *)(uintptr_t)BASE + K`. The check accepts BOTH;
   for the first the profile's `adr` is the named assumption that the handle local carries the
   window's base, for the second it is a theorem. **The witness below uses the spelling that is
   a theorem**, and the other one is named here so that nobody reads the chain as covering the
   emitted text without that premise.

---

## 4. The witness

*(`grammatik/Grammatik/KorrespondenzGeraetZeuge.lean`, 440 lines.)*

**The program was chosen after measuring.** The smallest corpus program with a register is
`beispiele/12-umlaufendes-register.gab` (31 lines, 12 code lines, one function); the smallest
with a register and no compound assignment is
`beispiele/113-register-traeger-ungeschrieben.gab` (32 lines, one function, two plain reads).
**Neither can be the witness**, and the reason is not the device: *no register-bearing corpus
program passes sieve (a)*, the Lean parser and elaborator, so there is no `Programm` in Lean
to certify. The witness is therefore a Lean fixture built to the SHAPE of `112`/`113` plus
`44`'s `else` — one `mmio` device, two registers, one function, all three device forms.

```
device Geraet(basis : u64) at mmio {
    reg ST   : u32 @0x00 class r  requires ST <= 8
    reg CTRL : u32 @0x04 class rw
}

impl fn treiber(a : u32) -> u32 {
    CTRL = a;                                       -- Stmt.regSchreib
    if (a < 1) { let s = ST; a = s; }               -- Block.regLies
    else       { let t = ST else (t < 9) { return 0; }   a = t; }   -- Block.regLiesElse
    return a;
}
```

and the C the certificate carries, row for row:

```c
uint32_t treiber(uint32_t v0) {
    (*(volatile uint32_t *)((volatile uint8_t *)(uintptr_t)0x40000000 + 4)) = v0;
    if (v0 < 1u) {
        uint32_t v1 = (*(volatile uint32_t *)((volatile uint8_t *)(uintptr_t)0x40000000 + 0));
        v0 = v1;
    } else {
        uint32_t v2 = (*(volatile uint32_t *)((volatile uint8_t *)(uintptr_t)0x40000000 + 0));
        if (!(v2 < 9u)) { return 0u; }
        v0 = v2;
    }
    return v0;
}
```

| theorem | says |
|---|---|
| `gZert_ok` | the certificate CHECKS — `korrOk gEL gFnum gZert gProg [()] gGT = true`, by `decide` |
| `gZert_sieb` | **SEVEN planted defects refused**: the device table switched off (`ein := false`), the wrong register (`ST`'s row at `CTRL`'s address), the wrong cell width (`uint16_t` at a `uint32_t` register), the promise read as its opposite (`t > 9` for `t < 9`), the `else` branch dropped, the `else` answer changed (`return 1;` for `return 0;`), and a plain local read where the volatile one stands |
| `gZert_ohneTafel` | the DEFAULT certificate call — the one the two closed chains make — refuses this program |
| `gerZeuge_nichtHardwareFrei` | the body is **not** `hardwareFrei`: the `korrOk` of before could not have certified it, and `rufAt_ohneHardware` does not apply |
| `gerAnn` | **the profile is INHABITED** — a term, so the chain is not vacuous |
| `gerZeuge_kette` | the callee relation between Gabbro's `treiber` and the C call, at every depth and budget |
| `gerZeuge_lauf` | **every run**: from a related state, when the Gabbro call ends in no model error, the C call has a run and every run of it ends related |

*A premise nobody can meet is not a premise, it is a hole.* `gerAnn` exists because the first
draft of this work had one: the profile carried
`∀ σ st, corrW EL σ st → st.live (.dev d) = true`, which reads well and is **false** for every
declaration with a register. It was found by trying to build the witness, and the repair is
§2.3.

---

## 5. Refused by name

| form | why not, and what it would take |
|---|---|
| **`Block.awaits`** (`sichtbarkeit`, A10) | `GRow` has no ATOMIC row at all — neither `CX.ald` nor `CS.astore` has one, and the `publish`/`awaits` pair would need both plus the payload list. `bsem_awaits` and `scorr_publish` are proved (H2/H3); what is missing is the rows and their hygiene, not the model. |
| **`Stmt.axiomCall` / `Block.bindAxiom`** (`annahme`) | needs a FOREIGN-CALL row (`CS.ext`) and, per axiom, the `AxCorr` premise (`CFormenH.lean` H5) — an assumption boundary, one per foreign function, that no certificate can decide. **And the corpus has ZERO axiom calls**, so nothing would be gained today: a driver call over the ABI is declared nine times and called never. |
| **`Stmt.forever`** (`fortschritt`, H2) | needs a loop row whose body may be left only through `goto m_ende`, and the watchdog line before it. `scorr_forever` is proved (F1); the row would have to carry the loop's own budget and its hygiene, which the `traverse` row does not model. |
| **an `else` branch that is not a `return`** | `Block.regLiesElse`'s `sonst` is a whole `Endblock`. A row that carried one needs the TERMINAL-block check inside the BLOCK check — a second recursion through a second type, and the staged recursion of `korrOk` must stay structural (`decide` has to reduce it in the kernel). The admitted `else` is the shape the one corpus instance writes (`beispiele/44:103`, `return Geraetelug::ZuTief;`). |
| **a `bool` register** | it cannot meet `GerAnnahme.rund`: `einpassen .bool n = some (n ≠ 0)` and `encW .bool` gives back `0`/`1`, so a raw `5` does not read back. An integer register meets it by `gerRund_int`. |
| **`transition`, the bank accessors, port I/O (`inb`/`outb`)** | no T4 lemma at all (`CFormenH.lean`'s CUTS say so); `portIn`/`portOut` have a memory model but no correspondence. |
| **the adequacy bridge for a device certificate** (`korrOk_endR`) | `BlockR` HAS both device constructors, but `BlockR.regLiesElse` is stated at `l = false` while the induction runs at every `l`. The bridge therefore carries `GT.ein = false`. Closing it means widening `BlockR.regLiesElse` to every loop flag — a change in `RufAdaequatRufG.lean`, which this lane did not touch. |
| **clause 4b of `schlusssatz` for a device certificate** | `korrOk_rufAt_ohneHardware` carries `GT.ein = false`, and it MUST: a register read is two of the five hardware sources. What a device chain would need instead is the hardware residue stated per outcome — *"no `Hardware` outcome except `register` at a declared register"* — which is a new theorem, not a weakening of this one. `hardwareFrei` itself was NOT weakened: `Stmt/Block/Endblock.hardwareFrei` are untouched, and `rufAt_ohneHardware` holds exactly as before for programs that avoid the five forms. |

---

## 6. Numbers

| what | measured |
|---|---|
| `lake build` over `grammatik/` | **0 errors**, **258 jobs**, whole library, on `ki-pc-fisch-101` (`gabbro-opus-ger`) |
| `#print axioms gabbro_ziel` | `propext`, `Classical.choice`, `Quot.sound` — **unchanged** |
| `#print axioms` of every new theorem | the standard three or fewer (`gZert_ok`, `gZert_sieb`, `gerAnn`: `propext`, `Quot.sound`; `gerZeuge_kette`, `gerZeuge_lauf`: the three) |
| `sorry` / `native_decide` / new `axiom` | **none** |
| `cargo test --no-fail-fast` | **25 collections, 0 failed** (the corpus collection alone 342 s) |
| `pruefe-exportlean.py` | **GREEN** — 30 of 30 exports, 0 Lean errors, 263 568 bytes elaborated |
| `pruefe-genlean.py` | **GREEN** — 2 of 2 generated files byte-identical, 18 927 bytes |
| `pruefe-cformen.py` | **GREEN** — 0 new uncovered forms, 0 unclassified statements, 0 missing lemmas, 0 missing assumptions |
| `pruefe-todo.py` | 14 findings / 7 stale numbers — **identical to the baseline** measured in a throw-away worktree at `83b6481c`, so none of them is this lane's |
| chain count | **2 of 113**, unchanged — sieve (a) binds, this lane touched sieve (e) |
| `corrW` sites moved | **17 of 300** |
| corpus programs with a device/axiom/`awaits`/`forever` form | **25 of 113** |
| corpus register reads with `else` | **1** |
| corpus axiom CALLS | **0** |
