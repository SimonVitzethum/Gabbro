# MUSE-REPORT-269: Emitter scope inventory

*Lane 269, wave A. Model: opencode-go/muse-spark-1.3-contributor. No delegation, no other model calls.*

## What was done

Wrote the owned deliverable `dokumente/x86/EMITTER-INVENTAR.md` (431 lines)
at commit base `09eed365`. Read in full or by exhaustive grep, deriving scope
from implementation branches only (never corpus frequencies):

- `grammatik/Grammatik/X86/Typen.lean` (87 lines): pilot vocabulary baseline
  (`Befehl` 14 constructors, `Breite`, permissions, `af = none` undefined).
- `crates/gabbro-syntax/src/ast.rs` (2559 lines): all `ItemArt` (~30),
  `TypExpr` (9), `ExprArt` (~14), `UnOp` (3), `BinOp` (19), `StmtArt` (~24),
  `CallTarget`, `Ordnung`, `Raum`, `Device/Bank/RegDecl/Uebergang`,
  `SyscallDecl/SysVarDecl/ZielDecl`, `Entry/Entrust/BootDecl`, `FnRumpf/AsmRumpf`.
- `crates/gabbro-check/src/emit.rs` (19250 lines, 259 `weigere` C001 sites):
  `emittiere/emittiere_mit/emittiere_mit_corr`, `ctyp/intty/breite_von/
  ganzzahlwort/schreibwort/lesewort`, `anweisung/traverse/match_*/forever/
  retry`, `holform/holwrap_form/holordnung`, `geraet/portzugriff/bank/
  uebergang/format_`, `kette_*/ketten_*`, `gleitkommatext/
  rechnet_mit_gleitkomma`, `ruf/intrinsik_c/fnzeiger_deklarator`,
  `syscall_befehl/syscall_stumpf/tor_inline_daten/kind_tor_falle`,
  `verbund/tabelle/arena/ops/markiert`.
- `crates/gabbro-cli/src/treiber.rs` (1722 lines): `GENERATOR_KENNUNG
  treiber-gen-10`, `erzeuge/erzeuge_metall/erzeuge_metall_voll/erzeuge_kmod`,
  `ARENA_LAUFZEIT/FADEN_LAUFZEIT/SPERRE_TICKET/BINDUNG_KOPF/KMOD_*`.
- `crates/gabbro-cli/src/bau.rs` (3125 lines): manifest words, `sammle/
  eintrittsregel/modulregel/bindungsregel*/treiberregel/metallregel/
  baue_einheit/prozess_start/metall_bild_binden/kmod_modul_binden`.
- Plan `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` §§0-5 and
  `dokumente/x86/WELLE-A.md`.

The document tables map source construct -> emitter/helper branch
(file/function/approx line) -> widths/layout/orders -> direct-x86 and proof
obligations, covering: aggregates, dynamic regions, strings, floats, indirect
calls, atomics/RMW/CAS orders, device/MMIO/DMA, syscalls, raw asm, interrupts/
start/join, generated runtime. Unreachable/refused paths are listed with their
checking evidence (N/M/C/LG codes, C001 sites); lowering helpers that must not
be erased are named. Arbitrary asm/foreign/loader bytes are explicitly exposed
as unbounded (§9). Reproducible method (§0 item 7) and six exhaustiveness gaps
(§12) are recorded.

## New definitions/theorems

None. Docs-only lane: no Lean file, no Rust change, no diagnostic/gift/example
numbers, MARKE_EMIT untouched.

## Last full check outcome

Docs-only task per wave rules: file/claim checks, no gratuitous cargo/Lean run
(one Lean build globally; coordinator owns integration).

- `dokumente/x86/EMITTER-INVENTAR.md`: exists, 431 lines.
- Claim check: all 23 cited emitter/driver/build function names resolve via
  `grep` over `emit.rs/treiber.rs/bau.rs` (missing: none).
- `git status`: only the new owned file untracked (plus this report);
  no other file touched.
- No `./lean-bau` / `./cargo-pruef` run (not required for a docs-only task;
  no code changed, nothing to keep green).

## What remains open

- All direct-x86 obligations in the inventory (§§2-8, §10): pilot covers only
  64-bit mov/add/sub/xor/cmp/load/store + relative jump/call/push/pop/ret.
  Missing per family: sub-word ops, lea/extensions, mul/div, logic/shifts,
  setcc/cmov, locked RMW/fences, SSE/SSE2, port/MMIO/trap/IDT forms,
  indirect calls, layout/ABI/image/TSO/cost/time proofs.
- Exhaustiveness gaps (§12): no match-coverage probe over AST enums vs emitter
  arms; C censuses do not measure x86; hand tables lack totality checks;
  template register is the single admission gate; asm/foreign stays refused
  by default.
- Line numbers are approximate at `09eed365`; function names are the stable key.

## Task correctness note

Nothing in the task is believed wrong. One clarification for the coordinator:
the wave-A table assigns lane 269 the inventory plus "widths/orders", which
this document covers via the helper tables (`ganzzahlwort/breite_von/intty/
storage`, `holordnung` pairs, `portbuchstaben`, trap table); the normative
width/order *proofs* belong to lanes 270-278 and are recorded as obligations,
not claimed here.
