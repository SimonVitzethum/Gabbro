# Adversarial implementation audit: FINAL-IMAGE

*Lane 407. Owns only this file plus `MUSE-REPORT-407.md`.
Scope: actual current implementations `Bild` / `Relokation` / `Byteschritt`
plus their stated consumer contract `dokumente/x86/IMAGE-ABI.md`.
No Lean, Rust, checker, emitter, goal or ledger change is made or claimed here.
Full source-to-final-byte validation remains OPEN.*

Reviewed tree state: files as read in this clone (branch `muse/407`;
`grammatik/Grammatik/X86/Bild.lean` 578 lines,
`Relokation.lean` 669 lines, `Byteschritt.lean` 510 lines,
`IMAGE-ABI.md` 675 lines). Line numbers below are as-read and may drift.
No behaviour is invented: every claim cites a file/theorem/line.
An explicitly OPEN bridge is recorded as OPEN, never as a bug.

Prior broad reviews (`REVIEW-GRUNDLAGEN.md`, `REVIEW-TSO.md`,
`REVIEW-OPT-BINAER.md`, `REVIEW-QUELLE-INVARIANTEN.md`, counter-review 308)
already cover architecture, trust boundaries and the full-binary obligation
schema. This audit does NOT repeat them. It covers only what the three
accepted modules actually check about the final relocated image, and the
concrete consumer gaps between them.

## 0. Verdict up front

1. **No false admission theorem found.** Every acceptance/refusal theorem
   checked here proves exactly what it states, over the vocabulary it
   imports. The positive witness (`zeugenBild_wohlgeformt`,
   `bildBss_wohlgeformt`, `bildParam_wohlgeformt`) and the refusal
   witnesses (overlap, wrap, outside entry, open relocation, rel32
   out-of-range, overlapping patches, altered opcode, truncated prefix,
   execute-denied) are real `decide` facts over concrete bytes.
2. **No helper admits a final image.** `Bild.wohlgeformt` is a decidable
   section/permission/entry/relocation-state check, `Relokation.patchAt`
   family is helper byte arithmetic with `relAnnahmeEndgueltig = false`
   (`relAnnahme_offen`), and `Byteschritt.byteschritt` steps the state it
   is given. Each file's CUTS says the coupling is OPEN, and the code
   matches the CUTS. That is hygiene, not a hole.
3. **The couplings a consumer needs do not exist yet.** Seven concrete,
   actionable gaps (F1–F7 below) sit exactly at the seams the task names:
   virtual-site versus file-offset patching, patched-byte re-decode,
   entry-as-decoded-start, image-accepts versus fetch-steps identity,
   section-kind permission schema, parametric absolute-site scan, and
   page-granularity executability. None is a second IR, none weakens a
   guarantee, and none is claimed closed.
4. **The residual loader is prose.** `geladen` is a pure function of the
   image; everything IMAGE-ABI sec. 11 demands of a real loader
   (segment equality, BSS zero-fill, exact reloc application, re-decode on
   the loaded mapping, entry predicates, stack/arena reservation, no
   widened executability through shared pages, three external-body
   obligations per leaving site) is unwitnessed by construction
   (`Bild.lean` CUTS lines 542–544). Any reading of the loaded-memory
   theorems as loader facts is the reader's error, not the file's claim.

## 1. What was read (and what was deliberately not re-read)

- `grammatik/Grammatik/X86/Bild.lean` (full, 578 lines).
- `grammatik/Grammatik/X86/Relokation.lean` (full, 669 lines).
- `grammatik/Grammatik/X86/Byteschritt.lean` (full, 510 lines).
- `dokumente/x86/IMAGE-ABI.md` (full, 675 lines; the consumer contract).
- `grammatik/Grammatik/X86/Typen.lean` (87 lines: `Byte`/`Wort`/`Adresse`,
  `Speicher` 41–45, `Befehl` pilot-14 53–68, `Decodiert` 70–73).
- `grammatik/Grammatik/X86/Speicher.lean` header + `lesbar8`/`schreibbar8`/
  `read64` (lines 21–48) and `addrOff` group facts (lines 52–72).
- `grammatik/Grammatik/X86/Codec.lean` header + `regCode`/`codeReg` (lines
  11–32) — only to confirm the decoder is the independent party both
  `Byteschritt` and IMAGE-ABI cite; no codec internals re-audited
  (lane 406 owns decode boundaries).
- `grammatik/Grammatik/X86/OverlapRefusal.lean` lines 1–120 (checker shape:
  `zugriffOk` takes a `Region`, not an `Abschnitt`) — only for the
  section/region seam (F5 consumer side).
- `grammatik/Grammatik.lean` lines 373–390 (all six names imported:
  `Ausfuehrung`, `Bild`, `Codec`, `Relokation`, `Byteschritt`,
  `OverlapRefusal` present).
- `dokumente/x86/WORK-ALLOCATION.md` sec. 1 dependency graph + rows
  C1/C2/C4/C5 (what is declared WAITING, so this audit does not demand it
  twice), `DIRECT-COMPILER.md` ledger rows 276/283/291/319 (accepted status
  of the three modules), `REVIEW-OPT-BINAER.md` sec. 0 verdict (to avoid
  duplicating the full-binary schema review).

Not re-read line by line: `Ausfuehrung.schritt` internals (lane 404 owns
arithmetic/flags), `TSO.lean` (lane 408), `Stapel`/`Regionen`/`EntryState`
candidates (lanes 409–411 own ABI/regions; C4 still candidate-pending per
ledger), optimiser/spec documents (friend-owned paths untouched).

## 2. What each module actually establishes (within its stated claim)

### 2.1 `Bild.lean` — correct within its claim

- Canonical profiles: only 48/57 exist (`Profil`, lines 16–24);
  boundary probes `kanonisch_tief_48`, `kanonisch_hoch_48`,
  `kanonisch_loch_48`, `kanonisch_57_weiter_als_48` (lines 98–116) are
  closed `decide` facts. A caller wanting another width needs a new
  constructor — loud, not silent.
- One checked mapping, file vs virtual kept apart: `fileReich` (125–127)
  vs `virtReich` (131–133), `ladenByte` (164–170) indexes
  `dateiByte bild.datei (s.dateiOff + (a - (bias + s.vaddr)))` (line 169).
  File offsets never become addresses directly. The parametric probe
  `bildParam_byte` (519–528) pins this: byte at `0x102000` under bias
  `0x100000` comes through the section, not through base + file offset.
- Decidable well-formedness `wohlgeformt` (260–272) checks, jointly:
  `groesseOk` (filesz ≤ memsz, 206–207), `dateiOk` (file containment,
  210–211), `virtuellOk` (no wrap under bias, 214–215),
  `kanonischBereich` per section (265), `ausrOk` (declared nonzero
  alignment dividing the biased base, 218–219), `wxOk` (W^X per section,
  222–223), pairwise file AND virtual disjointness (268–269), entry
  containment in an executable section (270 + `eintragEnthalten` 226–227),
  per-relocation `relokOk` (271), `modusOk` (272 + 255–257).
- Relocation state discipline: `relokOk` (240–251) refuses `offen` and
  `verweigert` (lines 245–246), bounds `siteOff < memLen` (line 248),
  then class-checks: `codeOperand` needs the *site's own section*
  executable plus `zielInCode` (line 250); `datenFeld` needs the site's
  section non-executable plus `zielInIrgendwo` (line 251). Unresolved is
  refused with a closed witness (`bildRelokOffen_verweigert`, 431–433).
- Loaded-memory facts are proved of the pure function `geladen`
  (192–196): `geladenByte_datei` (283–288), `geladenByte_bss` (292–296),
  `geladenLesbar_fund` / `geladenSchreibbar_fund` /
  `geladenAusfuehrbar_fund` (299–314), `ausserhalb_rahmen` (318–324).
  Memory-changing witness `schreibLese_zeuge` (454–477) goes through the
  shared `write64`/`read64` (reused, not remodelled) with
  `zeugenLesbar8`/`zeugenSchreibbar8` (443–450) as the permission facts.
- Refusal witnesses are non-degenerate and independent: overlap
  (`bildUeberlapp_verweigert`, 395–397), wrap (`bildUmbruch_verweigert`,
  411–413), outside entry (`bildEintrittAussen_verweigert`, 420–422),
  open relocation (above). BSS (`bildBss_wohlgeformt` 493–495,
  `bildBss_null` 498–502) and parametric bias (`bildParam_wohlgeformt`
  513–515) are accepted with their byte facts.

### 2.2 `Relokation.lean` — correct within its claim

- rel32 fit/encode/decode round-trip is proved generically:
  `rel32_rundgang` (75–89) over both signs, `rel32_adress_gleichung`
  (100–110) with the documented finding that the modular equation needs
  no wrap premises (lines 93–99), `rel32_next_rip` (115–120) carrying the
  exact no-wrap premise at next-RIP formation only, checked displacement
  `rel32Fuer` with refusal `rel32Fuer_verweigert` (133–137) and hit
  `rel32Fuer_trifft` (141–149). Boundary probes `sonde_rel32_oben/_unten/
  _ausserhalb/_negativ` (549–586) pin both edges and both just-outside
  values — out-of-range patches to `none`, never to wrapped bytes.
- abs64 values round-trip through the canonical split:
  `abs64_rundgang` (177–218) is exactly `bytesWort_wortByte`, no second
  codec. Probe `sonde_abs64_bytes` (600–603) pins little-endian order.
- Finite patching carries range/length/site/frame facts:
  `patchAt_bereich` (234–284), `patchAt_laenge` (287–335),
  `patchAt_stelle` (338–391), `patchAt_rahmen` (394–461); disjoint double
  patches refuse overlap (`patchZwei_verweigert`, 485–490) and preserve
  the first site (`patchZwei_erhaelt_erste`, 493–510). Probes
  `sonde_patchZwei_ueberlappung/_disjunkt`, `sonde_patchAt_ueberlauf`
  (611–626) are concrete.
- Site admissibility is LOUDLY open, not silently assumed:
  `relAnnahmeEndgueltig = false` (28) with `relAnnahme_offen` (32), and
  `patchAt` doc (222–226) states the image-plus-decoder proof decides
  code-operand vs data-field, never the caller. This matches IMAGE-ABI
  sec. 4 and contradicts nothing.

### 2.3 `Byteschritt.lean` — correct within its claim

- Fetch is the executable prefix of ACTUAL memory, capped at 15:
  `holeFetchAux` (31–36), `geholt` (40–41), length cap
  `holeFetchAux_laenge_le`/`geholt_laenge_le` (81–97), per-byte execute
  facts `holeFetchAux_ausfuehrbar`/`geholt_nur_ausfuehrbar` (121–149).
- Fetch gates on EXECUTE only, never data-read (`ausfuehrbarN` 23–25,
  `fetchDekodiert` 49–56, doc lines 20–22). The witness pins the
  distinction: `kette_mov_store_load` (339–346) ends with
  `ketteStart.speicher.lesbar 0x1000 = false` (line 344) — code executes
  without data-read permission — while `ohne_exec_verweigert` (396–399)
  refuses a readable-but-not-executable `ret`.
- Decoder is independent and checked at runtime:
  `fetchDekodiert_entspricht` (157–181) extracts decode equality, the
  `laenge + rest = fetched` equation, length validity and consumed-prefix
  executability. `kanonisch_schritt_ueberein` (227–252) proves canonical
  agreement for an arbitrary admitted instruction from round-trip
  instances, without needing the open arbitrary-input length soundness
  (CUTS lines 477–484 names exactly what is open).
- Byte-step correspondence is both directions:
  `byteschritt_weiter` (185–190), `byteschritt_verweigert_ohne_fetch`
  (195–199), `byteschritt_verweigert_ohne_schritt` (203–208), plus
  `fetch_nutzt_nur_praefix` (214–219). No halt constructor (doc 58–61);
  `verweigert` is absence of transition, fuel exhaustion answers
  `weiter` (`laufBytes` 274–279) — no termination claim.
- Negative/edge probes are real: altered opcode
  (`opcode_geaendert_verweigert`, 358–361, including the intact-bytes
  step to 4106 in the same conjunction), changed displacement moves the
  jump target (`sprungziel_folgt_byte`, 445–450), truncated prefix
  (377–379), boundary `ret` without over-read
  (`ret_an_grenze_ohne_ueberlesen`, 421–423).

## 3. Findings: seven seams, each with evidence and a concrete repair

Severity: P0 = a validator built only from these modules would admit or
break something the contract forbids. P1 = a missing bridge the wave plan
already books, sharpened to the exact lemma/function shape. No severity
above what is shown was found; in particular there is no invented
unsoundness in any proved theorem.

### F1 (P0): virtual-site check vs file-byte patch — different spaces, no glue

- Evidence: `Bild.relokOk` bounds the site as `r.siteOff < s.memLen`
  (line 248) — a *virtual-extent* check. `Relokation.patchAt` ranges over
  the *file list*: success implies `off + bs.length ≤ img.length`
  (`patchAt_bereich`, lines 234–235). No definition maps a `Relok`
  `(abschnitt, siteOff)` to a file offset (`dateiOff + siteOff`?), and no
  theorem connects `relokOk` to any `patchAt` application. A
  `codeOperand` site with `dateiLen ≤ siteOff < memLen` (the BSS tail)
  passes `relokOk` yet has no file bytes to patch; conversely a file
  patch at an offset the section mapping never loads changes bytes the
  machine never executes.
- Why this matters for "patching versus reviewed byte candidate": the
  reviewed candidate (`Codec.decode`/`Byteschritt.fetchDekodiert`) reads
  virtual/loaded bytes; the patcher writes file-list bytes. Without the
  glue, a validated-then-patched image and a patched-then-validated image
  are two different objects with no proved relation.
- Repair (missing bridge task): add the single-owner function the
  validator will actually call, e.g. `angewandt : Bild → Option (List
  Byte)` folding `patchAt` over `bild.reloks` via
  `dateiOff + siteOff` with the `siteOff + width ≤ dateiLen` (not
  `memLen`) side condition, and prove `patchAt_stelle`/`patchAt_rahmen`
  instances for it. Consumer: ValidatorSkeleton (C5, currently WAITING —
  this is its relocation half). Until then, `relokOk = true` must not be
  read as "the patched bytes are the reviewed bytes".

### F2 (P0): patched bytes are never re-decoded — the re-decode obligation is open on both sides

- Evidence: `Bild.relokOk` doc (lines 237–239) and CUTS (531–537):
  "Re-decoding of the patched bytes is OPEN, not checked here."
  `Relokation` CUTS (635–639): site admissibility "needs the checked
  image plus the decoder proof". Both sides point at each other; neither
  side performs the re-decode. IMAGE-ABI sec. 4 demands it twice
  (code-operand: "re-decodes the patched instruction and re-checks
  correspondence"; mode F: "plus re-decoding of every patched site").
- Concrete shape: `rel32Fuer_trifft` proves the four patch bytes decode
  back to the displacement — but not that the 15-byte window containing
  them still decodes to the same `Befehl` with the same length. A patch
  inside what the pre-patch decode called an operand field could, with a
  wrong site, overlap opcode/ModRM/prefix bytes; `relokOk` cannot see
  this because it never calls `decode`.
- Repair: the validator (C5) must state and prove, per patched image:
  `decode` before and after at the containing instruction agree on
  `Befehl`+`laenge` except for the intended operand value, and the new
  target satisfies `zielInCode`/decoded-start (F3). Negative probe to
  carry: a one-byte-shifted rel32 site that `patchAt` accepts and the
  validator refuses. This is legitimately incomplete deliverable work
  (both CUTS name it), not a false theorem.

### F3 (P0): entries and code targets are containment, not instruction starts

- Evidence: `eintragEnthalten` (226–227) and `zielInCode` (230–231) check
  `inAbschnitt bias s w && s.ausfuehrbar` — section membership plus
  executability. IMAGE-ABI secs. 5–6 demand more: every entry is a
  decoded instruction start with a checked entry-state predicate, and
  every direct-target computation
  `target = virtual_next_RIP + sign_extend(disp)` (virtual next-RIP,
  never a file offset) must land on a decoded start or a listed entry;
  mid-instruction/data/off-image branches are refused. `Relokation`
  already computes from virtual next-RIP (`rel32Fuer` doc lines 122–126:
  "`next` is the virtual address immediately past the decoded
  instruction, never a file offset") — but nothing checks the decoder
  half.
- Repair: entry/start bridge (C4 `EntryState` candidate + C5 skeleton):
  checked entry predicates per IMAGE-ABI sec. 5 list, plus a
  decoded-start table over executable sections that `eintragEnthalten`
  and `zielInCode` are refined against. Until then, an entry pointing
  mid-instruction inside an executable section passes `wohlgeformt`
  (witness: `zeugenBild` with `eintraege := [0x1001]` still satisfies
  `eintragEnthalten` — section `[0x1000,0x1004)` contains it). This is a
  validator-completeness gap, not an unsound acceptance theorem: the
  theorem proves containment, and containment is all it claims.

### F4 (P1): the accepted image is not the stepped state — `geladen` vs `Zustand.speicher` unlinked

- Evidence: `geladen` (192–196) builds a `Speicher` from `(bild, bias)`;
  `Byteschritt.geholt`/`fetchDekodiert`/`byteschritt` consume a
  `Zustand` carrying an arbitrary `Speicher`. No lemma instantiates a
  `Zustand` from a `wohlgeformt` image, and the witnesses prove it:
  `ketteSpeicher` (313–317) is hand-built (`bytesAusProg`, `ketteExec`,
  `ketteDaten`), not `geladen zeugenBild 0`. So today there is no proved
  path from "image accepted" to "fetch executes image bytes".
- Repair (small, high-value): prove the bridge lemmas the validator will
  reuse — from `wohlgeformt` + `abteilFinden = some s`, derive
  `ausfuehrbarN (geladen bild bias)` facts for code ranges and
  `lesbar8`/`schreibbar8` facts for data ranges, i.e. lift
  `geladenLesbar_fund`-family to the `*8`/prefix predicates
  `Byteschritt` consumes. Consumer: C5 skeleton + C4 entry states.
  Residual from IMAGE-ABI sec. 11 that stays prose even after the lemma:
  the real loader's mapping equality (file → mapping, BSS zero, exact
  reloc application, re-decode on the loaded mapping).

### F5 (P1): permission schema is W^X only — IMAGE-ABI sec. 3 demands more

- Evidence: `wxOk` (222–223) forbids writable+executable only.
  `wohlgeformt` does not require code readable, rodata non-writable AND
  non-executable, data/BSS executable-free, or guards non-everything.
  A data section `{lesbar := true, schreibbar := false,
  ausfuehrbar := true}` (readable-executable data) passes every
  `wohlgeformt` conjunct if disjoint/canonical/aligned — yet IMAGE-ABI
  sec. 3 forbids execution outside code and lists exact per-kind
  permissions (code R+X, rodata R, data/BSS R+W, guards none).
- Companion seam: `OverlapRefusal.zugriffOk` (lines 44–47) admits over a
  `Region`, not an `Abschnitt`; the section↔region layout connection
  (which access footprints belong to which section kind, spill slots
  proved thread-private per IMAGE-ABI sec. 8) has no lemma. `patchZwei`
  disjointness is file-offset intervals (Relokation 465–482), not
  virtual, permission- or decode-aware.
- Repair: decide the validator's permission schema per section kind
  (code/rodata/data/BSS/guard) as a `Bool` over `Abschnitt` and conjoin
  it to `wohlgeformt` (or a separate `valX86` layer per C5, to keep
  `Bild` stable); prove the section→region containment the overlap
  checker consumes. Negative probes to carry: R+X data section refused;
  store-to-rodata / exec-from-data refused at image level (today they
  fail only later, at `schritt` permission checks, if at all).

### F6 (P1): parametric mode misses its absolute-site scan; fixed mode misses its bias pin

- Evidence: `modusOk` for `.param b` checks only `b % 4096 = 0` (257).
  Range/nonwrap/canonicality/disjointness under bias ARE re-checked per
  section (`virtuellOk`, `kanonischBereich`, `paarweise (virtReich
  bias)` in `wohlgeformt`), which is good. What IMAGE-ABI sec. 4 mode P
  additionally demands — "every absolute site in the image must be a
  listed relocation of a bias-carrying kind; the validator decides this
  syntactically over the decoded image" — has no counterpart: no scan
  over decoded bytes for base-dependent absolutes exists (it cannot,
  without the decoder coupling of F2/F3). Fixed mode: `effBias .fest =
  0` (78–80) but nothing refuses calling `geladen`/`wohlgeformt` with a
  nonzero bias on a `.fest` image; "loading at any other bias without
  revalidation is refused" (IMAGE-ABI sec. 4 mode F) is prose.
- Repair: state both as validator obligations in C5 (absolute-site scan
  over the decoded image for mode P; bias-equality pin for mode F) with
  refusal probes. Legitimately open (C5 is WAITING per WORK-ALLOCATION);
  not a soundness hole in `modusOk`, which claims only the alignment
  conjunct.

### F7 (P2): page granularity and shared-page executability are absent

- Evidence: `Bild` has no page notion; sections carry byte extents plus a
  declared `ausr`. IMAGE-ABI sec. 11 loader contract is explicit:
  "page granularity is stated: leading/trailing partial pages keep the
  section's permissions for their covered bytes; the loader must not
  widen executability to a neighbouring section through a shared page."
  No definition states page coverage, and `paarweise (virtReich bias)`
  disjointness is byte-exact, so two sections sharing a 4096-page via
  adjacent byte ranges pass `wohlgeformt` while a page-granular loader
  would map them with one page's permissions.
- Repair: add the page-coverage function (floor/ceil to 4096) and prove
  either page-disjointness or the no-widening obligation as a validator
  check; carry a two-sections-share-one-page probe. P2 because it needs
  the loader mapping model first (sec. 11 formalisation), which is itself
  OPEN. Until then, images with page-sharing layouts must be refused by
  policy, not admitted by silence.

## 4. Residual loader assumptions (exact list — none of these is Lean-checked)

`geladen` CUTS (542–544): "`geladen` is a pure function of the image …
the loader contract is unwitnessed." The following IMAGE-ABI sec. 11
obligations therefore remain assumptions on any real loader, each a
refusal until discharged — quoted here so no consumer mistakes a proved
`geladen` fact for a loader fact:

1. Segment equality: every loadable section mapped at its checked
   address (F) or `base + vaddr` under the checked side conditions (P),
   with exactly its checked bytes, BSS tail zero-filled, exactly its
   checked permissions (sec. 11 para 1).
2. No widened executability through shared pages (sec. 11 para 1; cf. F7).
3. Relocations applied exactly: the loader applies exactly the checked
   `relocs` with the same values at the same virtual sites; post-load
   bytes at each site still decode as validated — re-decode on the
   LOADED mapping, not only on the file (sec. 11 para 2; cf. F1/F2).
4. External-body triple per leaving site (sec. 11 para 3): (a) checked
   declaration, (b) proved x86 caller-stub correspondence, (c) SUPPLIED
   Lean-proved callee contract at actual arguments/results/effects.
   Gate names, `assume` items and the historical `os_bindung_*` premises
   discharge nothing (secs. 11–12); images exercising gates without (c)
   are refused.
5. Entry handoff (sec. 11 para 4): control only to a listed entry with
   its predicate met (stack, alignment, BSS zero, arena reservations,
   single-threaded start shape); `gabbro_faden_start` sites match source
   sets.
6. No tool-correctness premise and no software-as-hardware (sec. 11
   paras 5–6): assembler/linker/loader/C-compiler/kernel correctness is
   checked by outputs, never assumed; hardware assumptions are
   silicon-only; OS/loader/runtime are user/binding logic with contracts.
7. Kernel-side and zero-fill gap records stay gaps (sec. 12, sec. 17):
   `os_bindung_*` family, storage/page-return zero-fill, `clone`
   register behaviour (only rcx/r11 destroyed), template x86-byte
   instances (`tor.*`, `faden.*`, `arena.dyn`, `sperre.ticket`,
   `start.nolibc`, module lifecycle — C-target instances exist, x86-byte
   correspondence OPEN per secs. 9–10), handwritten `start.S` /
   `METALL_EINTRITT` / module C helpers (validation + refinement per
   executed body, else refused).

## 5. Code/data overlap: what is covered vs what is not

Covered (proved, with teeth):

- Section-granular file AND virtual disjointness (`paarweise fileReich`,
  `paarweise (virtReich bias)`, `wohlgeformt` lines 268–269) with closed
  overlap refusal (`bildUeberlapp_verweigert`).
- W^X per section (`wxOk`), with no section both writable and executable.
- File-patch overlap refusal (`patchZwei_verweigert`) and first-site
  preservation (`patchZwei_erhaelt_erste`).
- Footprint-level conservative admission (`aliasZulassen`: only proved
  disjoint admits; same-footprint and unknown refused —
  `klassifiziere_verweigert_unbekannt`).

NOT covered (each maps to an F above, not repeated as a new claim):

- Within-section code/data overlap: instruction boundaries vs data
  objects vs padding vs relocation sites — needs the decoded-start table
  (F2/F3). `Bild` CUTS (531–534) states `abteilFinden` never looks at
  decoded bytes.
- Cross-carrier / unaligned / tearing shapes at image level — owned by
  the overlap/TSO bridge (lanes 342/408 + `OverlapRefusal` checker);
  the section→region wiring is the missing consumer lemma (F5).
- Patch-vs-patch across the file/virtual boundary (F1) and
  patch-vs-decode (F2).
- Page-shared executability (F7).

## 6. Probes: reproduced status

No new Lean file is owned by this lane and none was added; all probes
below are the committed theorems as read, cited with their locations.
`./lean-probe`/`./lean-bau` re-execution was attempted through the queued
wrappers; the execution tool was unavailable in this session (recorded in
`MUSE-REPORT-407.md`), so "reproduced" here means: statement read in full
in this clone, premises and conclusion verified by eye against the cited
lines, `decide`/`rfl` proof form confirmed, and no premise left unused.
Nothing below upgrades a `decide` fact into a chain claim.

Positive (acceptance with evidence):

- `Bild.zeugenBild_wohlgeformt` (356–358) + `zeugenFund_daten` (361–363)
  + `zeugenByte_geladen` (371–378) + `schreibLese_zeuge` (454–477):
  accepted two-section image with nonzero mapped byte and a
  memory-changing write/read-back through loaded memory.
- `Bild.bildBss_wohlgeformt` + `bildBss_null` (493–502): BSS accepted,
  tail reads defined zero through `geladenByte_bss`.
- `Bild.bildParam_wohlgeformt` + `bildParam_byte` (513–528): parametric
  bias accepted, byte maps through the section.
- `Relokation.rel32_rundgang` (75–89) + `sonde_adress_gleichung`
  (589–592) + `sonde_next_rip` (595–597): encode/decode round-trip and
  the virtual next-RIP equation on real addresses (4101 → 4096 via −5).
- `Relokation.abs64_rundgang` (177–218) + `sonde_abs64_rund` (605–609).
- `Byteschritt.kette_mov_store_load` (339–346): MOV/STORE/LOAD from
  actual bytes moves 42 to `rcx`, cell 8192 zero → 42.
- `Byteschritt.kanonisch_schritt_ueberein` (227–252): canonical agreement
  for an arbitrary admitted instruction.

Negative (refusals with evidence):

- `Bild.bildUeberlapp_verweigert`, `bildUmbruch_verweigert`,
  `bildEintrittAussen_verweigert`, `bildRelokOffen_verweigert`
  (395–433): one independent witness per shape.
- `Relokation.sonde_rel32_ausserhalb` (577–580) +
  `sonde_rel32Fuer_verweigert` (583–586): just-out-of-range refused both
  ways; no wrapping.
- `Relokation.sonde_patchZwei_ueberlappung` (612–615) +
  `sonde_patchAt_ueberlauf` (624–626).
- `Byteschritt.opcode_geaendert_verweigert` (358–361),
  `praefix_abgeschnitten_verweigert` (377–379),
  `ohne_exec_verweigert` (396–399), `sprungziel_folgt_byte` (445–450)
  (changed byte ⇒ changed target, the positive direction of the same
  sensitivity the image validator must inherit after F2).

## 7. Prioritised repair / missing-bridge tasks (for the coordinator queue)

1. **P0 — relocation application glue (F1):** one owner function
   `Bild → Option (List Byte)` + `siteOff + width ≤ dateiLen` discipline
   + `patchAt_stelle`/`rahmen` instances. Unblocks C5's relocation half.
2. **P0 — patched re-decode + decoded-start table (F2+F3):** per-site
   before/after `decode` agreement + entry/target membership in decoded
   starts; entry predicates (C4) consume the same table. Unblocks C5's
   coverage half and IMAGE-ABI secs. 5–6.
3. **P1 — `geladen`-to-`Zustand` bridge (F4):** lift permission-agreement
   facts to `lesbar8`/`schreibbar8`/`ausfuehrbarN` over loaded ranges.
   Small; unblocks fetch-from-image reasoning.
4. **P1 — permission schema + section→region wiring (F5):** per-kind
   permission `Bool`, conjoined at validator level; containment lemmas
   into `OverlapRefusal.zugriffOk`. Unblocks data-exec and spill-privacy
   reasoning at image level.
5. **P1 — bias discipline pins (F6):** mode-P absolute-site scan (needs
   F2/F3) + mode-F bias-equality refusal. States as C5 obligations now,
   proofs after the decode table.
6. **P2 — page-granularity model (F7):** page-cover function +
   no-widening obligation, after the sec. 11 mapping formalisation.
7. Explicit non-tasks (do NOT file as repairs): an `UNKNOWN-overlap`
   admission, a loader-correctness premise, a software-as-hardware
   assumption, a per-program rule, trust in an emitter annotation for
   length, or any claim that C-target template lemmas discharge x86-byte
   correspondence (IMAGE-ABI secs. 9–10, 17 forbid each).

## 8. What this audit is not

- Not a second architecture review: the full-binary schema, TSO bridge
  shape, optimiser obligations and source-bridge design stay with lanes
  274/275/277/281/292–294/308 and their reviewers.
- Not a decoder, concurrency, ABI, region, float or cost audit: lanes
  404–406/408–413 own those seams; this file cites their interfaces only
  where the image consumes them.
- Not a bug invention exercise: every OPEN item above is OPEN in the
  cited CUTS or the cited IMAGE-ABI gap section. Where a module is
  correct within its stated claim (sec. 2), this audit says so.

---

*CUTS: prose audit only. No Lean definition, theorem, proof, decoder,
validator, refinement, cost-transfer or final-image acceptance is proved
here. All couplings in sec. 3 (F1–F7) and every loader obligation in
sec. 4 remain OPEN. File/theorem/line evidence is as-read in this clone;
line numbers may drift. No new hardware, software or tool-correctness
premise is introduced or assumed.*
