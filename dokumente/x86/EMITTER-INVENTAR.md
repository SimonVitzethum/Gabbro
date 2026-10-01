# Emitter scope inventory — direct x86-64 validation (wave A, lane 269)

*Owner: lane 269. Owned file per `dokumente/x86/WELLE-A.md`.
Commit measured at: `09eed365` (short hash; `git log --oneline -3` in report).
No compiler change in this lane; no MARKE touched; no numbers allocated.*

## 0. Method (reproducible)

All scope below is derived from implementation branches and source
constructs, never from corpus frequencies or example binaries.

1. Read the canonical pilot vocabulary once:
   `grammatik/Grammatik/X86/Typen.lean` (87 lines; namespace
   `Gabbro.Grammatik.X86`). It defines `Byte`/`Wort`/`Adresse` as
   `BitVec 8/64/64`, 16 registers in architectural encoding order,
   `Breite = b8|b16|b32|b64`, `Flags` (with `af : Option Bool`,
   undefined not false), `Speicher` (byte contents plus
   read/write/execute permissions), `Zustand`, and exactly these
   `Befehl` constructors: `movImm64`, `movReg64`, `addReg64`,
   `subReg64`, `xorReg64`, `cmpReg64`, `load64`, `store64` (both
   base-register plus sign-extended `BitVec 32` displacement),
   `jump32`, `jumpIf32`, `call32`, `push64`, `pop64`, `ret`.
   No other width, form, decoder, TSO rule, ABI fact or cost fact is
   in the pilot.
2. Read the AST enumerations in full:
   `crates/gabbro-syntax/src/ast.rs` (2559 lines):
   `ItemArt` (~30 variants), `TypExpr` (9 variants), `ExprArt`
   (~14 variants), `UnOp` (3), `BinOp` (19), `Ort`/`OrtSuffix`,
   `CallTarget` (Path/Place), `StmtArt` (~24 variants), `Schleife`,
   `XForm`, `Ordnung` (Acquire/Release/Seq/Relaxed), `Raum`
   (Normal/Mmio/Dma/Code/Boot/Port/Benannt), `Device`/`Bank`/
   `RegDecl`/`Uebergang`, `SyscallDecl`/`SysVarDecl`/`ZielDecl`,
   `EntryDecl`/`EntrustDecl`/`BootDecl`, `FnRumpf`
   (Block/Pred/Asm/Keiner), `AsmRumpf` (free-text lines + in/out/
   clobbers), `Format`/`Endian`, `ArenaDecl`, `AtomicDecl`,
   `LockDecl`, `Tabelle`, `Reason`, `Assume`/`Axiom`, and
   manifest-level words in `crates/gabbro-cli/src/bau.rs`.
3. Walk every emission path in
   `crates/gabbro-check/src/emit.rs` (19250 lines, 259 `weigere(`
   sites emitting `C001 no lowering`):
   entry points `emittiere` (~line 1054), `emittiere_mit` (~1068),
   `emittiere_mit_corr` (~3321); per-item dispatch (~3141+ and the
   second item walk ~1000-2600 for name/constant tables); per-type
   `ctyp` (~7106), `intty` (~6610), `breite_von` (~6277),
   `ganzzahlwort` (~6261), `schreibwort`/`lesewort` (~6323/~6348);
   per-statement `anweisung` (~10409), `traverse` (~13738),
   `match_*` (~14013-14476), `forever` (~12873), `retry` (~12451),
   atomics `holform` (~13197), `holwrap_form` (~13107),
   `holordnung` (~13325); devices `geraet` (~4727),
   `portzugriff` (~5129), `bank` (~5242), `uebergang` (~5470),
   `format_` (~5745); strings `kette_*`/`ketten_*` (~6842-7020);
   floats `gleitkommatext` (~17393), `rechnet_mit_gleitkomma`
   (~945); calls `ruf` (~16385), `intrinsik_c` (~16711),
   `fnzeiger_deklarator` (~6653); gates `syscall_befehl` (~9276),
   `syscall_stumpf` (~9284), `tor_inline_daten` (~8926),
   `kind_tor_falle` (~9148); aggregates `verbund` (~4066),
   `tabelle` (~4194), `arena` (~4297), `ops` (~4526),
   `markiert` (~4158).
4. Read the generated drivers in
   `crates/gabbro-cli/src/treiber.rs` (1722 lines):
   `GENERATOR_KENNUNG = "treiber-gen-10"`, `erzeuge` (~417,
   hosted), `erzeuge_metall`/`erzeuge_metall_voll` (~555/~569,
   bare metal), `erzeuge_kmod` (~1065, kernel module),
   `ARENA_LAUFZEIT` (~168), `FADEN_LAUFZEIT` (~279),
   `SPERRE_TICKET` (~328), `BINDUNG_KOPF` (~248), `KMOD_ARENA`,
   `KMOD_STDATOMIC`, `KMOD_MELDECODES`, `kmod_koepfe`,
   plus pin counters `faden_start_zaehlung`,
   `metall_start_zaehlung`, `pin_pruefe`.
5. Read entry/link code in `crates/gabbro-cli/src/bau.rs`
   (3125 lines): manifest words (`kmod`, `provision`, `note`,
   `nolibc`, `unit`, `metal`, indented file paths),
   `modulkarte`/`sammle` (~523/~565), `nolibc_haken` (~816),
   `eintrittsregel` (~825), `modulregel` (~949),
   `bindungsregel_gehostet` (~1070), `bindungsregel` (~1286),
   `treiberregel` (~1453), `metallregel` (~1596),
   `baue_einheit` (~2305), `prozess_start` (~2713, nolibc
   `_start`), `metall_bild_binden` (~2773),
   `kmod_modul_binden` (~2846).
6. Cross-check the active plan `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md`
   sections 0-5 (source-to-bytes chain, T1-T5, §2 instruction
   families, §3 W/GX reuse with per-access TSO bridge, §4 order
   step 1 = this inventory, §5 trust base) and
   `dokumente/x86/WELLE-A.md` (shared contract, pilot limits,
   lane owners, gates).
7. Re-measure command set (run from repo root):
   `wc -l crates/gabbro-check/src/emit.rs
   crates/gabbro-syntax/src/ast.rs crates/gabbro-cli/src/treiber.rs
   crates/gabbro-cli/src/bau.rs`;
   `grep -n "^\(pub \)\?enum \|^\(pub \)\?struct "
   crates/gabbro-syntax/src/ast.rs`;
   `grep -n "fn [a-z_]*" crates/gabbro-check/src/emit.rs`;
   `grep -c "weigere(" crates/gabbro-check/src/emit.rs`;
   `grep -n "__asm__\|syscall\|memory_order\|atomic_" 
   crates/gabbro-check/src/emit.rs`.

Line numbers above are approximate at `09eed365`; function names
are the stable keys. Where a checker code is named (N/M/C/LG/H
codes in messages), it is quoted as checking evidence, not as
proof.

## 1. Pilot coverage baseline

The pilot proves nothing about execution yet (see its CUTS), but it
fixes the vocabulary every later obligation is stated in:

- Data widths: `Breite.bits/bytes`; only `load64`/`store64`/
  `movImm64`/`movReg64`/`addReg64`/`subReg64`/`xorReg64`/
  `cmpReg64` exist. There is NO 8/16/32-bit data operation, NO
  `lea`, NO extension, NO multiply/divide, NO logic beyond xor,
  NO shifts/rotates, NO carry, NO `setcc`/`cmovcc`, NO locked RMW,
  NO fence, NO SSE/SSE2, NO port/MMIO/syscall/interrupt form.
- Control: only `jump32`, `jumpIf32` (over the 16 `Bedingung`
  codes), `call32` (relative, address after decoded instruction),
  `push64`/`pop64`, `ret`. No indirect call/jump, no IDT entry,
  no fault delivery.
- Memory: byte-addressed with per-address R/W/X bits; loads and
  stores are 64-bit only at base+sign-extended-disp. No
  sub-word/overlapping/tearing rule, no stack-frame discipline, no
  TSO/store-buffer rule, no device semantics.

Consequence used in every row below: any source construct whose
correct lowering needs a form outside this list has an OPEN
direct-x86 obligation (new `Befehl`/decoder/memory/ABI/proof),
even where the C backend already emits working code.

## 2. Items: source construct -> emitter branch -> x86 obligation

| Source item (`ast.rs ItemArt`) | Emitter/helper branch | Widths / layout / orders | Direct x86 + proof obligations |
|---|---|---|---|
| `Modul`, `Use` | name/module maps only (`Namen`, `modulkarte`/`sammle` in `bau.rs`); no C | none | Source-fidelity only (T3): resolution must be computed in Lean from source; no machine code. Linking obligation belongs to lane 277/TSO-bridge. |
| `Typ` (`Verbund`, aliases, tagged `markiert`, `Varianten`) | `verbund` (~4066), `markiert` (~4158), `ctyp` record arm (~7119ff) | C `struct` with declared field order; layout is the C compiler's (offsets pinned by `_Static_assert` in prelude) | Full layout obligation OPEN: field offsets, padding, alignment for every aggregate must be fixed in the image contract (lane 276) and each field access proved to its address computation (`lea`+width, missing from pilot). |
| `Konst` (incl. const tables `ArrayLit`, string max) | `konst_zertifikate`, `const_table`/`const_wert_zeile` (~3862-3995), `cbreite`/`czahl` fences | Value must fit C type (`i128` fence; `cbreite` table: 4 for 32-bit/float, 8 for 64-bit/double) | Read-only data section + relocation obligation (lane 276); float consts need IEEE bit obligation (lane 278). |
| `Statisch` (scalar/array, `aligned N`, sections) | `statischer_kopf` (~739), `feldstatisch` (~12646), `abschnitt_attribut` (~698) | C `static` with section attribute; alignment word honoured | Data layout + permissions (writable vs read-only) + alignment/tearing obligations; `aligned N` needs proof the loader honours it. |
| `Funktion` (Block body) | `funktion` (~8265), `prototyp_kern` (~8113), `eigene_ruempfe` (~8244), `anweisung`/`ausdruck` | Signature via `ctyp`/`fnzeiger_deklarator`; calling convention is the C ABI today | Calling-convention + frame + spill obligation OPEN: direct backend must fix its own ABI (lane 276/277), prove arg passing, caller/callee-saved registers, stack alignment (16B), return-value channels including `or R`/`never`. |
| `Funktion` with `Asm` body (`FnRumpf::Asm`) | `funktion` asm arm (~8481): one `__asm__ __volatile__` block, `asmtext` escaping (~7537), `_Noreturn` for `-> never`, fall-off refusal | Free text + declared `in/out/clobbers` + `arch`; `memory` clobber default | **Unbounded by construction (see §9).** A bounded ISA profile cannot cover arbitrary template text; each `asm` body needs refusal or per-site validation with its contract. Pilot has no asm form. |
| `extern fn` (`FnRumpf::Keiner`) incl. variadic `...` (N573) and fn-ptr params (N574) | prototype only (`prototyp_kern`); foreign body linked from manifest `.c`/binding | C prototype; `...` marker; fn-ptr declarator fix (name inside declarator) | Foreign code is outside the validated image unless its bytes are validated too (§9). Indirect-call ABI for fn pointers needed (no indirect `call` in pilot). |
| `Format` (bitfields, endian) | `format_` (~5745), `schrittbits` (~5594), `bitwort` (~5706), `lesewort`/`schreibwort` (~6348/~6323) keyed by `breite_von`+endian | Widths 8/16/32/64 + little/big endian words (`ganzzahlwort` table); `_ => 8`/`int64_t` fallbacks removed, now `None` | Bit-level layout + endianness + tearing obligations; needs 8/16/32-bit accesses + shifts/masks in the profile (§2 data family). |
| `Tabelle` (slots, invariants, `ops`) | `tabelle` (~4194), `ops` (~4526: generated insert/remove/count fns), slot `ruecksetzwert` (~4473) | One C struct per table + storage array; `count = hi` slots; `used` global for arenas | Object layout + bounds obligation per access; `ops` helpers are generated code that must itself be validated (lane 276/277 templates T5). |
| `Reason` (incl. `pub` since network wall 1) | reason enum emission; `verbundmarken`/`fall_belegt`/`varianten_*` | C enum + payload union where applicable | Tagged-value layout obligation; `or R` channel needs control-flow proof (two exits). |
| `State` / transitions | `pruefkoerper`, no direct C state machine (proof device) | none | Source-duty obligation (T1); no direct machine code except through functions that read/write the carrier. |
| `Device` (`at port/mmio/dma`, regs, banks, mirrors, transitions) | `geraet` (~4727), `portzugriff` (~5129), `geraetelesung` (~5178), `bank` (~5242), `ausdruck_geraet` (~5299), `uebergang` (~5470); `at port` requires `arch x86_64` in unit (~4815) | Port widths 8/16/32 only (`portbuchstaben` ~5084; no wider port form); `at mmio` lowered, `at dma` refused (needs barrier statement); bank = accessor functions over run-time base | Hardware-form profile OPEN (§2): only required port/mmio forms to be admitted, each with a wrapper proof over checked contracts (user/binding logic) + named silicon/device-response semantics only; DMA/MMIO need own semantics, never inherit RAM/TSO rules. No port/MMIO form exists in pilot. |
| `Assume` / `Axiom` / `Check` | headers/assumption lists; `assume` as `D.Annahme` in exporter; no C | Named hardware text (`arch`-gated, falsifier or reason per `ast.rs Assume`) | Trust-base obligation (§5): `assume`/`axiom` items carry named HARDWARE behaviour only (silicon/device/timing — never OS/kernel behaviour; see the historical gaps in §12 item 7); checks are proof duties (T1). |
| `Atomic` (`AtomicDecl`, ordering word) | `atom_declarator` (~6797, `_Atomic T name` / arrays), `atom_refusal` (~6813), ordering pair table (~1318-1332: Release/Acquire->release/acquire pair, Seq->seq_cst, Relaxed/None->relaxed) | C11 `_Atomic` + `memory_order_*`; K11.2.3: `release/acquire/seq` on the checked fragment lower as stated, with unfalsifiable visibility note | Per-access TSO bridge OPEN (lane 274): every declared order needs lowering proof to lockedRMW/fence/ordinary-access; `seq_cst`-as-release/acquire abstraction is NOT a proved total order (plan §3). Pilot has no atomic form. |
| `Lock` / `Rcu` / `Gruppe` / `Concurrent` / `Accumulates` / `Walk` | lock tables in `Namen`; `erzeuge*` lock words (ticket); `accumulates` fold refusal for strings; walk lowering via `baumsicht`/`vorfahren`/`nachfahren` | Ticket lock C (`SPERRE_TICKET`); rank order from `LockDecl` | Lock-template correspondence (`sperrAbstrakt`, ticket proof reuse + concrete sequence proof); RCU/group/walk need family extensions (plan §4 step 5). |
| `Entry` (`vector`/`via`/`arch`/regs/stack/`pro_kern`/`dispatch`) | `bau.rs eintrittsregel` (~825); metal driver entry stubs; `hat_fehlercode` (`treiber.rs` ~81) | Vector const range; register pin names; stack symbol | Entry-calling-convention + fault-delivery obligation (T5 templates); no interrupt/IDT form in pilot; needs lane 276/277 image-entry contract. |
| `Entrust` / `Boot` (steps `Ruf`/`Setzt`) | `bau.rs` boot/dispatch wiring; `metall_bild_binden` | Boot order = declared step order | Whole-image init obligation (lane 276): only validated bytes run before dispatch; `Setzt` needs width/layout proof. |
| `Syscall` / `SysVar` / `Ziel` (gate + per-target binding) | `tor_inline_daten` (~8926), `kind_tor_falle` (~9148), `syscall_befehl` (~9276: ABI->trap table), `syscall_stumpf` (~9284: pinned `register __asm__("reg")` locals, `__asm__ volatile syscall`, `-4095` errno fence, `or R` decode, region answers C186, stack-gate trampoline C187, clone N572) | Register map per gate; trap per (abi,arch); errno fence at `-4095`; costs `1+n` | Checked gate/binding contracts per gate (user logic: `requires`/`ensures`/`effects`/`costs`, total `errors` decode) + named silicon trap semantics only (what the trap instruction itself does); trap/exception return not in pilot; stack-gate/child-region/trampoline needs control+memory proof (template `tor.*`, `faden.*`); region answers need extent proof (N571/N463). |
| `Profil` / `ProfilBedarf` | manifest/profile checks in checker (`N217/N219`); no C | none | Hardware-profile binding obligation at link/accept time (the profile references named hardware assumptions only), not machine code. |
| `Arena` (`capacity lo..hi`, element type) | `arena` (~4297: static table of `count=hi` + `used` global), `braucht_arena_dynamisch` (~15449), generated arena runtime (`ARENA_LAUFZEIT`, `KMOD_ARENA`, `provision` pool) | Static: `count=hi`; dynamic: reserve/commit below ceiling, `provision` bytes multiple of 4096, page-size query | Allocator-template proof + ceiling/OOM-branch proof (`else` always owed for `grow`); page-return (`region.leeren` via the binding's `gabbro_os_leeren`) needs a checked binding-library contract (user logic — the mapping effect is kernel work covered by that contract, never an assumption); unbounded-region opt-in: finite image and unbounded runtime allocation are distinct (see §6). |

## 3. Types and widths

| Type form | C lowering (branch) | Width/layout/order facts | x86 obligation |
|---|---|---|---|
| Integer `uN/iN` words | `ganzzahlwort` (~6261: exhaustive table, `None` for unknown), `intty` (~6610), `breite_von` (~6277), `storage`/`storage_ctyp` (~14922/~14937) | 8/16/32/64-bit signed/unsigned; `int` taken as 32-bit (fence noted ~3970); `u64::max`/`i128` fences in const paths | Needs 8/16/32/64 data ops + extensions + overflow/stop semantics (§2 integers); wraparound only via declared `Wrapping` (`SlotTyp::Wrapping` -> `intty`), saturating via `saturation_c`; mixed-sign policy `vorzeichenlose_namen_hier` is per-function scope. |
| `bool` | `_Bool`/C `bool` | 1-byte logical value | Compare/`setcc` + branch obligation; `&&`/`||`/`!` are control, not just ALU. |
| `f32`/`f64` (+ range, NaN/inf bits) | `float`/`double` (~6682-6693, `primitivwort` f32->float/f64->double); `gleitkommatext` bits; `rechnet_mit_gleitkomma` prelude pins (`float.h`, DBL checks ~906-929); mixed float/double arithmetic refused (`ist_gemischt_float_double`) | IEEE binary32/64; rounding: `rounded` word required for inexact literals | SSE/SSE2 scalar profile + rounding/exception/NaN/control-state binding to existing IEEE model (lane 278); no float form in pilot. |
| `never` (`-> never`) | `_Noreturn void` | No return path; asm-`never` must not fall off | Control-flow coverage: every path ends in diverging gate/trap; needs validator check, not just type. |
| Named (`Pfad`), `Index` | `ctyp` path arm; index = generated index type from table `count` | Same width as aliased carrier | Follows carrier obligation. |
| Array `[T; N]` (`Feld`/`ArrayTy`) | C array; `feld_deklarator` (~12592), `feldlaenge` (~4123), `feldlaenge_von` (~14621) | Length const; element C type | Bounds proof per index (M103/N463/N571 family); needs address-scale (`lea`/shift) + width. |
| `ptr<raum, w> T` (incl. `Code`, `Boot`, named spaces) | `zeiger_schreibend` (~6708), `raumqualifizierer` (~6754), `zeigerziel` (~7619); pointer index answers pointee (`umgebung` fix, no new code) | Space qualifier; const-correctness for `restrict` (`darf_restrict` ~7580); raw int->ptr is refused (M140) | Address-calculation + space-permission obligation; `Code`/`Boot` pointers are X-region addresses (lane 276); byte pointers have no G form (OFFEN O37). |
| `Verbund` (struct fields) | `verbund` struct + `verbundlokale`/`verbundwert`/`verbundmarken` helpers (kept: lowering-introduced, do not erase) | Field order as declared; offsets by C compiler + `_Static_assert` pins | Fixed layout + padding proof; each field projection = address add (needs `lea`). |
| `Varianten`/`markiert` (sums, tagged) | `markiert` enum+payload; `match_markiert`/`match_option`/`match_grund` | Discriminant + payload layout | Discriminant-branch proof; payload access after tag check. |
| `FnZeiger` | `fnzeiger_deklarator` (~6653; name inside declarator) | C fn-ptr declarator | Indirect-call ABI obligation; no indirect call in pilot. |
| `string max N` / `Kette` literal | `ktyp`/`ketten_max`/`kette_wert`/`kette_zu`/`kette_seite`/`ketten_abschnitt` (~6842-7020); `gabbro_string_N` value type; string section spliced at `ketten_marke` (~2030/~3255) | `max` byte bound; literal length = UTF-8 byte count; adjacent texts NOT joined | Bounded-buffer + length proof; string section is image data (lane 276); unbounded strings have no form (refused). |
| Ghost/spec-only positions | `ist_geist` (~875); kept in maps but no C | none | No machine obligation; must not leak into image (validator must check erasure). |

## 4. Expressions

| Expr form | Emitter branch | Remarks for x86 |
|---|---|---|
| `Zahl`, `Wahr`/`Falsch` | `zahltext` (~6627), `czahl` fences; const evaluator `constexpr_value` | Immediates (`movImm64` covers 64-bit ints; bool/char widths need narrower moves). |
| `Gleitkomma` | `gleitkommatext` (~17393) | SSE const-pool/data obligation (lane 278). |
| `Ort` (place: base + suffixes, index, field, deref) | `ort` (~16873), `lese_bytes`/`schreib_bytes` (~14799/~14824), `byte_traeger` (~14697), `index_ist_rein` | Address + bounds + width + space + atomicity/tearing per access (plan §3 first bullet); overlapping accesses need byte-memory reasoning (lane 271). |
| `FnWert &f`, `Grund R::F` | value constructors; no call | Code-address / tag-value data obligation. |
| `Ruf` direct (`CallTarget::Path`) | `ruf` (~16385), arg passing `argsTo_of`-shape, `prototyp_kern` positions | Call ABI + arg-width proof; `let-else` over fallible (`or R`) gates = two-exit control. |
| `Ruf` indirect (`CallTarget::Place`) | lowers to itself as C indirect call (~16386 note) | **No indirect-call form in pilot**; needs target-set + ABI + X-permission proof. |
| `LibraryCall @lib#fn(args){region}` | refused `N057` (region uninterpreted `RawToken`) | No obligation until region translation lands; must stay refused. |
| `Eingebaut` (intrinsics) | `intrinsik_c` (~16711), `intrinsik_breite`/`ctyp_breite` (~16809/~16863) | One small closed table; each intrinsic needs its own instruction proof (most have none in pilot: no mul/div/shift). |
| `Klammer`, `Alt(old)`, `Ergebnis(result)` | parens erased; `old/result` are spec-only | Spec evaluation only; `old/result` must not emit code. |
| `Zaehle` (count) | generated count fn of the table's `ops` | Same as callee obligation. |
| `Unaer` (`!`, `-`, `~`) | `ausdruck` unary arms; `~` width-sensitive (needs carrier width) | `!` = test/setcc+branch; `-` = neg (missing); `~` = width-masked not (missing widths). |
| `Binaer` (6 comparisons, `&& \|\|`, `& \|\ ^`, `<< >>`, `+ - * / %`, wrap `+% -% *% <<%`, sat `+sat`) | `ausdruck` binary arms; `wrap_c`/`saturation_c` (~15218/~15253), `wrap_form`/`wrap_shift_form`, `storage` selection; mixed float/double refused | Pilot covers only 64-bit add/sub/xor/cmp. Missing: mul/div/mod, all shifts/rotates, and/or, extensions, carry, sat/clamp, FP arithmetic. Each needs §2 integer/FP admission with overflow/division/stop proof. |
| `ArrayLit [...]` | const-table only (`const_table`); never a body value | Data-section obligation only. |
| `Kette "..."` | `kette_wert`/`kette_zu` into string section | Bounded-copy obligation. |

## 5. Statements and blocks

| Stmt form | Emitter branch | x86 relevance |
|---|---|---|
| `Let` / `LetSonst` (`let x [:T] = e [else]`) | `anweisung` let arms; `let_tyexpr` (~7954), `lokale_lets` (~7983), annotated-type check (M101/M135) | Local slot/frame allocation + spills (lane 271/275); `else` = second exit edge. |
| `Zuweisung` (`=`, `op=`, incl. `zeigerArithmetik`/`doubleTyp` compound forms) | assign arms (~10643ff); `assignDurch`/`assignSlot`/`assignVar`/`assignGlob` shapes; float-width suffixing | Width + atomicity per store; compound read-modify-write is NOT atomic (needs TSO bridge; only declared atomics are). |
| `Wenn` (if/else) | `anweisung` if arm + `sprungziele` (~12947) | Conditional-branch proof over flags (only 64-bit cmp in pilot; narrower compares missing). |
| `Match` (int/int-bound/tagged/option/reason) | `match_int` (~14476), `match_markiert` (~14013), `match_option` (~14213), `match_grund` (~14134), `intpat_werte`/`int_grenze` | Jump-table vs branch-chain lowering choice must be validated per image (not per source); bounds/refusals (N411ff family) stay refused. |
| `Schleife` (bounded loops), `Traverse` (table walk), `Forever`, `Retry` (bounded retry with `retry_schranken` ~3637) | `traverse` (~13738), `forever` (~12873), `retry` (~12451), loop-bound checks | Termination/budget/cost obligations (goal `FortschrittG`/`ZeitAb`); unrolling/motion are untrusted opts needing certificates (lane 275). `traverse` with non-literal bound is refused (only literal provably equals `count`). |
| `Bricht`/`Leave`/`Next` (`breaking`, `leave`, `next`) | break/next arms with label threading | Control-target proof (addresses after decoded insns, not annotations). |
| `Narrow` (range check with `else`) | `verenge` (~15783), index-bound helpers, per-function unsigned set `vorzeichenlose_namen_hier` (~6214, per-function scope) | Checked-cast = compare+branch+diverge; widths needed per bound. |
| `Sperrt` (`locks`), `Observiert` (`observes`) | lock acquire/release around body; return-inside-locks evaluates value BEFORE release (~10409-10609) | Lock-template sequence proof (ticket) + visibility; RCU read-side needs family proof. |
| `Publish` / `AwaitLoad` / `Exchange` (payloads, `XForm`) | `atomic_store_explicit` / `atomic_load_explicit` / RMW-loop emission (~11193-11692, ~13186: `add`=single `lock xadd`, or/and/xor-with-used-old-value=`cmpxchg` loop) | Ordering-pair proof per site (`holordnung`); payload rule (O25 wall) stays open where stated; relaxed+payload falls to `relaxed_mit_last` with explicit question. |
| `Return` (value / bare / fall-off-void) | return arms incl. lock-release-after-value | Epilogue + calling-convention proof; fall-off only for void. |
| `Ruf` statement / `LibraryCall` statement | `ruf`; library refused `N057` | Same as expression calls. |
| `Alloc` / `ResetArena` / `ResetSlot` / `Grow` / `Child` / `Start` | `arena` + `ResetSlotStmt` (`reset X at i count n` via program binding `gabbro_os_leeren`+`madvise`), `grow` commit below ceiling, `child` inline with dead fall-through mark, `start` refused `C001` until lowering (driver owns creation) | Allocator + page-return + child-on-handed-stack + thread-start obligations (T5); `start` has no inline machine code by design. |

Ghost/spec helpers that lowering introduced and that must NOT be
erased as "unreached": `verbundlokale`, `verbundwert`,
`verbundmarken`, `vorzeichenlose_namen_hier` (per-function scope),
`let_tyexpr`, `feldlaenge(_von)`, `traegertyp`, `grenzzahl`,
`indexschranke`/`ausdruck_obergrenze`, `wert_ctyp`/`register_ctyp`,
`laufzicht`/`baumsicht`, `ohne_klammern`, `rumpf_antwortet`/
`rumpf_scheitert`/`rumpf_gibt_wert`. They are the width/bound/
scope facts the validator will need; unreachable/refused paths
are marked at `weigere` sites, not by deleting these helpers.

## 6. Aggregates, dynamic regions, strings

Covered above; summary for the proof planner:

- Aggregates (`Verbund`, `Tabelle`+`ops`, `Varianten`/`markiert`,
  `Format`, `Statisch`/`Konst` arrays, const tables): every field/
  slot access is base+offset×width with possible padding. Needs
  lane-276 fixed layout + per-access width/bounds proof. No
  aggregate form is "free" on x86.
- Dynamic regions (`Arena lo..hi`, `alloc`/`reset`/`grow`,
  `provision` pools, `KMOD_ARENA`/`ARENA_LAUFZEIT`): monotone
  allocation with refuse-on-full; `reset` starts a generation and
  stales prior indices; `grow` commits below ceiling or runs
  `else`. Needs allocator-template proof + OOM-edge proof + cost
   accounting. Unbounded-region opt-in (plan §2: Turing completeness
   in the abstract model; physical hardware stays finite) is NOT outside
   validation: the finite code image (bytes, layout, entries) is validated
   like any program, and what the opt-in changes is stated separately —
   the static whole-program memory bound is lost for such a program
   (every allocation may fail and must be handled), with memory/time
   coverage following the declared contracts instead of a ceiling.
 - Page return (`ResetSlot` = `region.leeren`): zero-read +
   whole-page return through the program's own `gabbro_os_leeren`.
   Needs a checked binding-library contract (user logic — the mapping
   effect is kernel work covered by that contract, never an assumption);
   arena slots are
   write-once so give-back does not apply there (measured reason,
   kept).
- Strings (`string max N`, `Kette`, `gabbro_string_N`, string
  section): bounded copies with length-vs-max proof; section is
  image data with relocations.

## 7. Floats

`f32`->`float`, `f64`->`double`; prelude pins (`float.h`, range
checks) whenever `rechnet_mit_gleitkomma` holds (any float type,
table slot, or format field). Mixed `float`/`double` arithmetic
is refused (would compute in `double` against the `f32` fact).
Out of range/stop behaviour, rounding (`rounded` word), NaN/inf
bits, and SSE control state follow the existing IEEE model; the
direct profile must bind scalar SSE/SSE2 per admitted op with
rounding/exception/NaN proof (lane 278). Pilot has no FP form.

## 8. Indirect calls, atomics/RMW/CAS/orders

- Indirect calls (`CallTarget::Place`, `FnZeiger` values `&f`,
  `entry fn` code type N575-N577, foreign fn-ptr params N574):
  emitter lowers indirect to C indirect and refuses what it
  cannot type (N574/N575-N577 gifts cited in AGENTS §7). Pilot
  has no indirect call/jump; needs target-set discipline +
  ABI + X-permission proof. Never treat a call sequence as
  indivisible without a linearisation/commutation proof (plan §3).
- Atomics: declarations (`atom_declarator`), element-type gate
  (`atom_target`, `atom_elem_typ`; strings excluded), fetch forms
  (`holform` closed table + `holwrap_form` gate-needs-type rule),
  single ordering per site (`holordnung`: declared pair or
  `relaxed`), publish/await/exchange templates, `retry` bounds,
  ticket-lock runtime (`SPERRE_TICKET`: `gabbro_ticket_nimm/gib`
  over `pause`-carrying spin). C11 orders in the C backend are:
  relaxed/acquire/release/seq_cst spellings. Direct-TSO work
  (lane 274): map each to ordinary/locked-RMW/fence + retry-loop
  proof; successful vs failed `cmpxchg` differ; `add`=`lock xadd`,
  others=`cmpxchg` loops (comment ~13186); W `seq_cst`-as-acq/rel
  is not a total order -- document limits, validate promised
  guarantees, keep forbidden-outcome probes.

## 9. Foreign and unbounded code (cannot be covered by a bounded ISA profile)

Explicitly exposed; none of this may enter a finished chain by
declaration alone (plan §0/§5):

- `asm` bodies (`AsmRumpf.zeilen` free text + `ein`/`aus`
  constraints + `zerstoert` clobbers): emitted verbatim as
  `__asm__ __volatile__` with operand lists. Arbitrary template
  text is unbounded; the bounded profile can only refuse it or
  admit enumerated templates with per-template machine-checked
  proofs (register `gabbro schablonen --tor`; templates
  `tor.*`/`start.*`/`arena.*`/`sperre.*`/`faden.*`/`modul.*` are
  the admitted set, each with its proof -- new templates only
  through that register).
- `extern fn` declarations without bodies + manifest file lists
  (indented `.c` paths, `binding` `.h` shims, `bibliothek/`
  units, per-target `linux.c`/`linux-kmod.c` remnants where they
  still exist): linked foreign bytes are unvalidated until their
  final bytes pass the validator. The `bindungsregel*` checks
  (W7 shared check) keep the interface closed, but do not validate
  the foreign bytes.
- `LibraryCall` regions (`Vec<RawToken>`, braces only): refused
  `N057`; uninterpreted by design.
- Manifest `kmod`/`provision`/`note`/`target`/`metal` wiring and
  loader actions (`metall_bild_binden`, `kmod_modul_binden`):
  image construction itself must satisfy the lane-276 contract
  (entries, relocations, loaded mapping = validated image).
- `assume`/`axiom` bodies and `arch`-gated promises: named HARDWARE
  assumptions only (silicon/device/timing — never OS/kernel behaviour,
  never code).

## 10. Devices, syscalls, interrupts, start/join, generated runtime

- Devices: `at port` (in/out widths 8/16/32, `__asm__ volatile`
  with `memory` clobber, `arch x86_64` required), `at mmio`
  (lowered address access), `at dma` (refused: barrier choice is
  a memory-model statement), banks (accessor fns over run-time
  base; C driver calls them), transitions (proof device + emitted
   step code), mirrors/params (checked maps). Each admitted
   hardware form needs a wrapper proof over checked contracts
   (user/binding logic) + named silicon/device-response semantics
   only; MMIO/DMA/
   cache/device observations get their own semantics, never silent
   RAM inheritance (plan §3).
- Syscalls: per-gate number (constexpr, may name a const),
  `regs in/out`, `stack r` (handed stack, N446/N447, N572),
  `clobbers` (declared + `memory`/`rcx`/`r11` for the trap),
  `errors` total decode over `or R` with explicit errno numbers,
   `requires`/`ensures`/`effects`/`costs` (missing costs = N322,
   cost-opaque) are checked gate/binding contracts — user logic, never
   assumptions; only what the trap instruction itself does (register
   effects incl. `rcx`/`r11`, privilege transition) is named silicon
   trap semantics. `syscall_befehl` maps (abi,arch)->trap; current
  traps are raw `syscall` via `__asm__` (+ `goto` into region
  label for stack gates; `tor.kind` outlines the child region as
  `gabbro_kind_<nr>` -- no `asm goto` into the parent frame).
  `syscall_stumpf` pins registers (`register ... __asm__("reg")`),
  issues the trap, fences at `-4095`, decodes errno into `or R`,
  handles value/region/stack answers (C186/C187). All of this is
  C-backend evidence; the direct profile must re-prove each
  wrapper against the decoded trap bytes.
- Interrupts/entries/boot: `EntryDecl` (vector const, `via`,
  `arch`, regs in/out, preserves/clobbers, stack, `pro_kern`,
  `ist`, nesting, dispatch path), `EntrustDecl`, `BootDecl`
  steps. Checked by `eintrittsregel`/`modulregel`/`treiberregel`/
  `metallregel`; emitted entries are driver stubs + dispatch
  calls. Needs T5 entry-template correspondence incl. declared
  roots and fault delivery (`hat_fehlercode` table).
- Start/join/concurrency: `concurrent` sets + `start {..}`
  (checker-resolved, emitter-refused inline) + drivers own
  creation/join: hosted `FADEN_LAUFZEIT` over stack gates
  (`gabbro_os_klon_tor`, flags, `futex` wait, `exit`), metal
  per-root 64K stacks + `wort_*` join words, kmod kernel
  threads. `N_WURZELN` counts declared starts (pin-checked).
  Needs start/join/publication proof against `sperrAbstrakt`
  and declared roots; private stacks/spills must be shown
  race-free (plan §3).
- Generated runtime roots (all in-image code, all must be
  validated when the backend switches): `ARENA_LAUFZEIT`
  (reserve/commit/page-size over gates + falsifiers),
  `FADEN_LAUFZEIT` (clone/wait/exit over gates),
  `SPERRE_TICKET` (ticket lock), `BINDUNG_KOPF`,
  `KMOD_*` (module arena/lifetime/`stdatomic` mapping onto
  `READ_ONCE`/`WRITE_ONCE`/acquire/release/`try_cmpxchg`),
  `prozess_start` nolibc `_start` (align `rsp`, call
  `gabbro_os_anfang`, hand status to `gabbro_os_ende`),
  metal `start.S`/`kern.c` interplay via `metall_bild_binden`,
  module init/exit via `kmod_modul_binden`.

## 11. Refused / unreachable paths (checking evidence)

A path is listed here only with the rule that refuses it; the
validator must keep refusing it until its family lands (§4 step 5):

- `LibraryCall` in either position: `N057` (region untranslated).
- Inline `start` statement: emitter `C001` (driver owns threads).
- `at dma` device access: refused by name (barrier is a
  model statement); `at port` without `arch x86_64`: refused.
- Module with floating-point `atomic`: refused (kernel FP rule);
  `atomic` in `module` generally: narrowed from blanket to FP-only,
  rest lowered (K6).
- Variadic marker at Gabbro fn / record behind `...`: N573
  (`extern.variadik`); foreign param carrying fn-ptr: N574
  (`fremd.ohne_code`); `entry fn` misuse trio: N575-N577
  (`eintritt.code`).
- Stack-gate without `child` region / child misuse: N572
  (`klon.uebergabe`); stack gate without trampoline regs: C187;
  region answer without `or R`: C186.
- Manifest-level refusals (no `Satz`, no N code by the session-6
  reading): entry/binding/kmod/provision/nolibc shape errors in
  `bau.rs` (`eintrittsregel`, `bindungsregel*`, `modulregel`,
  `nolibc_haken`), plus exporter `LG` codes for gate shapes
  without Lean form (LG001/LG002/LG003/LG004/LG007 families).
- `traverse` with non-literal bound; `alloc` without `else` where
  owed / at wrong block level; mixed float/double arithmetic;
  int->ptr / int->fn-ptr (M140); unbounded strings; `!`-family
  and cast shapes outside `korrOk` (C-backend sieve, kept as
  regression, not as x86 evidence).
- 259 emitter `C001 no lowering` sites (`weigere`): each names
  the unlowered shape instead of guessing. A site disappearing
  without its family proof is a regression, not progress.

## 12. Exhaustiveness gaps (open by construction)

1. No machine-checked enumeration ties `ItemArt`/`StmtArt`/
   `ExprArt`/`TypExpr` variants to emitter arms; a new variant
   with a catch-all refusal is silent scope loss. Gap: add a
   generator-level exhaustiveness probe (match-coverage check
   over the AST enums vs `emittiere_mit`/`anweisung`/`ausdruck`/
   `ctyp` arms) owned by the coordinator, not this lane.
2. `korrOk`/`CFormen`/`pruefe-cformen.py` census the C backend,
   not x86 bytes; `zaehle-kette.py` counts C chains. None
   measures x86 coverage. Gap: a new byte-image census (lane 276)
   must replace them for the selected target; do not relabel them.
3. Width table (`ganzzahlwort`), trap table (`syscall_befehl`),
   port-width table (`portbuchstaben`), ordering table
   (`holordnung` pairs), intrinsic table (`intrinsik_c`) are
   hand-maintained maps. Gap: each needs a totality proof or a
   refusal-completeness check against its input enum.
4. Driver/runtime templates (`ARENA/FADEN/SPERRE/KMOD_*`,
   `prozess_start`, metal/kmod binders) evolve with
   `GENERATOR_KENNUNG`; the inventory pins `treiber-gen-10`.
   Gap: template register (`gabbro schablonen --tor`) must be
   the single source of admitted templates with proofs.
5. `asm`/foreign/loader bytes are unbounded (§9). Gap: keep them
   refused-by-default; admit only proved templates.
6. TSO/ABI/image/cost/float/time families have no pilot facts
   (lanes 271-278 own them). This inventory records the
   obligation; it does not discharge any of them.
7. Historical OS-knowledge in code and bindings (existing gaps, not
   intended architecture). The standing rule (plan §§3/5; AGENTS.md
   §3) is: OS/kernel/scheduler/runtime/binding behaviour is user
   logic with checked contracts, never an assumption; only
   silicon/device/timing behaviour is a named assumption. Two
   existing spots predate or stretch that rule and are recorded here
   as gaps to close, not as architecture:
   (a) `assume os_bindung_null` (`bibliothek/linux/linux.gab:54`,
   falsifier `sonde_os_null`): the zero-read promise of the
   binding's reserve/commit/page-return service is carried as a named
   `assume` (the file's own comment calls it "its own assumption").
   Intended: the mapping effect is covered by the binding library's
   checked gate contracts (the `linux_os_*` gates below it already
   are Gabbro, checked like user code), with no OS-behaviour
   `assume`.
   (b) Linux errno knowledge baked into the emitter:
   `syscall_stumpf` hardcodes the `-4095..-1` decode fence
   (`emit.rs` ~9220 `if (gabbro_roh_{lo} < -4095)`, ~9047/~9695
   `(1..=4095)` maps, ~9834 "past the Linux `-4095` bound", ~9703
   "the kernel's error"). Intended ("nothing knows an operating
   system"): the decode is derived from each gate's declared
   `errors` map, naming only the silicon trap semantics.

## 13. What this inventory does and does not claim

It claims: every reachable emission path above was read off the
implementation branches named, with widths/layouts/orders as the
helpers compute them, and every unbounded/foreign path was named
   instead of hidden. Attribution rule applied throughout:
   OS/kernel/scheduler/runtime/binding behaviour is user logic with
   checked contracts; only silicon/device/timing behaviour is a named
   assumption (plan §§3/5). It does not claim: any x86 correspondence,
any TSO/ABI/layout proof, any accepted byte chain, or any
performance figure. There is no completed direct-x86 chain
(plan §4 measurement); the two closed C chains remain legacy
evidence only.

*CUTS (inventory lane): no Lean theorems; no decoder/memory/ABI/
TSO/float/cost proofs; no per-access mapping; no image contract;
line numbers approximate at the pinned commit; exhaustiveness
checks of §12 remain open.*
