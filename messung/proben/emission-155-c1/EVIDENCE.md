# emission-155-c1: witness pairs for the C1 declaration trio

Scope: the three closable C1 slots of the open rows in
`grammatik/Grammatik/Erhaltung.lean` `tafel`, in tafel order:
`cTypedef`, `cDefine`, `cEnum`. Pointer arithmetic and `#include` stay open;
section 4 books both as scope-withdrawn with reason. The ruled C2/C3 forms of
the parallel lane are not touched.

Method: one witness PAIR per slot (two minimal units, two emitter shapes each),
each emitted with the worktree binary (`gabbro emit`, exit 0 for all six), each
emission compiled with `cc (GCC) 16.2.1` on x86-64 as
`cc -std=c11 -O0/-O2 -Wall -Wextra -Werror -c` (12 of 12 green, 2026-09-11).
No emitter change was made, so every existing emission is byte-identical by
construction; the pin below is the enforcement.

## 1. Witness pairs

| unit | pinned shape in the emission | verdict |
|---|---|---|
| `emission-155-ctypedef-record.gab` | `typedef struct { ... } Paar;` over a two-field record | admit, ruled in `messung/CFORM-REGEL-TYPEDEF.md` |
| `emission-155-ctypedef-table.gab` | `Schlange_slot` plus `Schlange` plus `Schlange_NONE (N)` | admit, ruled in `messung/CFORM-REGEL-TYPEDEF.md` |
| `emission-155-cdefine-width.gab` | `#define BREITE 8u`, reused as the table count | admit, ruled in `messung/CFORM-REGEL-DEFINE.md` |
| `emission-155-cdefine-plain.gab` | `#define K 41u`, read as `K + 1` | admit, ruled in `messung/CFORM-REGEL-DEFINE.md` |
| `emission-155-cenum-reason.gab` | `typedef enum { ... } Fehler;` over a two-variant channel | admit, ruled in `messung/CFORM-REGEL-ENUM.md` |
| `emission-155-cenum-mark.gab` | `typedef enum { ... } Anfrage_marke;` plus the struct with the union | admit, ruled in `messung/CFORM-REGEL-ENUM.md` |

Why no lowering and no refusal, per slot (from the ruling notes, not re-measured
here): the `typedef` expansion buys nothing at any level while scattering 240
single definition points; the enum-free spelling keeps the values and drops the
closed list the `switch` without `default` is checked against; inlining every
`#define` at its read buys nothing while scattering 210 single definition points.

## 2. Verification

| unit | pruefe | emit | cc -O0 | cc -O2 |
|---|---|---|---|---|
| `emission-155-ctypedef-record.gab` | 0 errors, 0 hints | exit 0 | clean | clean |
| `emission-155-ctypedef-table.gab` | 0 errors, 0 hints | exit 0 | clean | clean |
| `emission-155-cdefine-width.gab` | 0 errors, 0 hints | exit 0 | clean | clean |
| `emission-155-cdefine-plain.gab` | 0 errors, 0 hints | exit 0 | clean | clean |
| `emission-155-cenum-reason.gab` | 0 errors, 0 hints | exit 0 | clean | clean |
| `emission-155-cenum-mark.gab` | 0 errors, 0 hints | exit 0 | clean | clean |

One repair on the way: the record half first summed two bare `u32` fields and
fell at `M104`/`M101` (result width without room). The fields now carry
`in 0 .. 1000` where they are declared, the shape the refusal text itself names;
the C1 form under test (the `typedef`) is untouched by the repair.

## 3. Lean flips

`grammatik/Grammatik/Erhaltung.lean`, status field only, one row per slot, each
citing its ruling note; no `def`, theorem, or proof touched:

- `cTypedef` to `aufListe` (alias only; layout fixed once)
- `cDefine` to `aufListe` (object-like macro only; typed reads)
- `cEnum` to `aufListe` (closed alternative list as int)

The debt proof `tafel_nicht_geschlossen` still rests on `zeigerArithmetik`
(section 4), so it closes by the same `decide` with no proof change.

## 4. Scope-withdrawn, with reason

- `zeigerArithmetik` (C1, 491 sites) stays `offen`. The lane-142 refusal went
  back out the same day it landed: it fired on `u32` arithmetic in
  `messung/netz/udp-echo.gab` because `wert_ctyp` resolves through scope-blind
  maps (`crates/gabbro-check/src/emit.rs`, the `zeigerArithmetik WITHDRAWN`
  note). A refusal that fires on integers is not strict, it is loaded. Returns
  with per-function scoping; see `messung/EMIT-SICHTBARKEIT.md`. Deciding this
  slot is a checker-scoping task, not a status-field flip.
- `cInclude` (C1, 408 sites) stays `offen`. The four-line preamble is
  load-bearing line by line (lane-142 drop-one-include `cc` runs fail on
  `uint32_t`, `bool`, atomics, `isfinite`); no alternative spelling exists, and
  refusal would break every unit including the gift corpus. There is no ruling
  note for this slot, and admitting the preprocessor wholesale is a ruling of
  its own, not a flip. Booked for a lane with a `CFORM-REGEL-INCLUDE.md`.
