# MUSE-REPORT-386: Independent exact-candidate C4 review of 348 EntryState

Lane 386, branch `muse/386`. Clone verified: `/home/simon/Dokumente/gabbro-muse/a386`,
branch `muse/386`. Review target: snapshot `.tmp/review/author-348/` (OWNER-TASK,
MUSE-REPORT-348, PATCH.diff, BUILD-EVIDENCE.json, candidate `EntryState.lean` +
umbrella). No other clones read, no network, no agent calls. Staged the candidate
module privately for one `./lean-probe` run, then removed it; tree clean except
this report.

## Method

- Read the full 553-line candidate against the ACCEPTED canonical modules in this
  clone (`Typen`, `Speicher`, `Bild`, `Stapel`, `Gleitprofil`): every reused name
  resolved with matching signature and argument order.
- Mechanical scans for `sorry` / `native_decide` / `unsafe` / tactic-`admit` /
  `axiom`: zero hits (the 10 `admit`-grep hits are the English word "admits" in
  doc comments).
- Private staging: copied the snapshot file to
  `grammatik/Grammatik/X86/EntryState.lean` in this clone (whose base is NEWER
  than the author's) and ran `./lean-probe`: `0 error(s)`, all `#print axioms`
  at most `[propext, Quot.sound]`, matching the author's BUILD-EVIDENCE
  (`./lean-bau` exit 0, 386 jobs). File removed afterwards;
  `git status` clean before this report.

## What the candidate delivers (verified, not just claimed)

- Checked entry admission `Bool`s over canonical vocabularies only: `EintrittArt`
  (8 kinds), `EintrittZustand` (canonical `Zustand` + `MXCSR` + touch/save bits +
  IF + guard finding), `eintrittOk`, `externZielOk`, `trapRueckOk`,
  `KernAntwort` (named-only, no theorems). No new instruction semantics, no
  `schritt` duplication, no second IR or executor.
- Canonical reuse confirmed: `ladenLesbar/Schreibbar/Ausfuehrbar bild bias a`
  call order, `eintragEnthalten bias secs e` order, `Flags.af = none`,
  `MXCSR = BitVec 32` with `0x1F80` valid per accepted `mxcsr_standard`,
  `zeugenBild.eintraege = [0x1000]` = witness RIP, `lesbar8/schreibbar8` each
  cover 8 bytes so one-word `stapelRW` at `top-8` covers `[basis, top)`,
  witness stack `[0x7000,0x8000)` RW non-executable, guard probe `0x6000`
  unmapped, `0x8000` 16-aligned.
- Joint witness `eintritt_zeuge`: accepted hosted entry AND a real
  memory-changing write (`write64` 42 at stack basis, `read64_nach_write64`
  read-back, byte difference via `writeBytesN_hit` + `addrOff_null`).
  Non-degenerate (loaded image + RW stack + nonzero write). HARD-RULE-13's
  strict trigger does not fire (no `Vertrag`/`Stmt`/… premises); the witness
  exceeds the owner task's demand anyway.
- Refusals proved by `decide` on concrete states (XMM-without-save,
  missing guard, non-entry external target `0x5000`, manifest-without-bytes,
  wrong IF, misaligned RSP `0x8001`, unlisted RIP) plus generic component
  lemmas whose every hypothesis is rewritten into the goal; the
  `unfold; rw; simp` refusal shape matches accepted practice
  (e.g. `Byteschritt.lean`). No `Prop`-typed premise, no `intro _`, no
  quantified-away contract, no conclusion-as-premise.
- Safety corrections honoured: refusals are admission `Bool`s (stated);
  16-alignment only at the call boundary (stated in CUTS, unaligned ordinary
  accesses not faulted); narrow/DIV/float/LOCK/TSO/source-bridge/cost all
  listed OPEN in CUTS; kernel behaviour named only; manifest row without
  validated bytes admits nothing (`trapRueckOk` + proved refusal).
- Owned paths: PATCH.diff touches exactly `MUSE-REPORT-348.md`, one ADDITIVE
  umbrella import (`+import Grammatik.X86.EntryState`), and the new module.
  (Note for merger: author's base predates `SpillPrivate`, so the snapshot's
  full umbrella file lacks that line; the PATCH hunk itself is purely
  additive — standard import-union at merge per AGENTS.md §9.)

## Minor notes (not defects, no repair demanded)

- Report says "no auto-bound implicits", but `trapRueck_verweigert_ohne_bytes`
  leaves `gesichertBytes` to auto-binding (`{gesichertBytes : Bool}` implicit).
  Legal Lean, elaborates green, premise used — suggest an explicit binder next
  touch; the theorem stands as is.
- `KernAntwort.unbekannt` is never constructed; harmless named placeholder,
  honestly labelled OPEN.
- `externZielOk` does not conjoin `wohlgeformt`; safe direction for a target
  check used inside an already-checked image context, no contrary claim made.

## Open items (candidate's own CUTS, endorsed)

Single-probe guard (no 4096-byte sweep), one-word stack window (no
frame/red-zone/per-CPU), save/guard/bytes flags as validator findings (no
validated byte sequences, no XMM file), no decoder/indirect-target
certificates, no source correspondence, no TSO bridge, no cost transfer, no
final-byte closure, shared-IR consumer pending. Bounded claim is truthful.

CANDIDATE: 348 cd5c9899f1786dbe359f3b96ba024deed897f70c
VERDICT: ACCEPT
