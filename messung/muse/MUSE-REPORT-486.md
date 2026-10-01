# MUSE-REPORT-486: Independent exact-candidate review of 406

- Clone: `/home/simon/Dokumente/gabbro-muse/a486`, branch `muse/486` — verified.
- Candidate: 406 head `46a19a189e533deff2184d5dacb58aae63239926`, base `0b3132b7`
  (base commit exists locally; candidate object not in this clone, so the review
  uses the supplied `.tmp/review/SNAPSHOT.json`, `author-406/PATCH.diff`,
  `author-406/dokumente/x86/AUDIT-DECODE-BOUNDARY.md`, and `BUILD-EVIDENCE.json`,
  cross-checked against the actual sources in this clone).
- Owned file only: `MUSE-REPORT-486.md`. No other clone read. Scratch probe
  (`.tmp/probe486_check.lean`) reproduced then deleted; working tree clean.

## What was checked

1. **Scope/ownership**: `PATCH.diff` (300 lines) touches exactly the two pinned
   files (`MUSE-REPORT-406.md`, `dokumente/x86/AUDIT-DECODE-BOUNDARY.md`).
   Docs-only: no `grammatik/`, Rust, or config change, so no axiom, witness,
   `gabbro_ziel`, guardian, or emission impact is possible. No second IR, toy
   model, vacuous theorem, or safety weakening exists in the candidate.
2. **Source fidelity** (verified by reading in this clone):
   - `Codec.lean` 806 lines / `Byteschritt.lean` 510 lines match the report.
   - First-byte dispatch disjointness (195/232/233/15/65/72,73,76,77/80-87/88-95,
     `Codec.lean` L403-453), movImm window 184-191 vs ModRM opcodes, mod-3/mod-2
     split with opcode-139 register-direct falling to `none` via `decodeRegReg`'s
     catch-all (L326) — confirmed. One nit: the audit attributes that `none` to
     L365-372; it actually fires one call deeper. Substance correct.
   - `Decodiert` is a bare `(befehl, laenge)` pair (`Typen.lean` L70-73), 14
     `Befehl` constructors (counted) — confirmed.
   - Sole `Codec` consumer is `Byteschritt` (grep: only umbrella + `Byteschritt`
     import it); `byteschritt` takes only state; `schritt` trusts a caller pair
     modulo `laengeOk` (`Ausfuehrung.lean` L69-72); `fetchDekodiert` enforces the
     runtime length equation — confirmed.
   - `roundtrip` (L561), `roundtrip_len_ok` (L581), `encode_len` (L279) exist;
     the three §6 open statements are verbatim in the files' own CUTS
     (`Codec.lean` L783-792, `Byteschritt.lean` L460ff, incl. the exact
     length-soundness formula) — the audit duplicates nothing, assigns P0 to
     scheduled lane 435 without collision.
   - `Bild` decoded-starts OPEN booking confirmed in its CUTS (text matches;
     line numbers off by ~2 against my newer HEAD — immaterial drift).
   - `DIRECT-COMPILER-DESIGN.md` L116 "codec round-trip is PROVED" matches the
     scoped theorems — confirmed (file at repo root, as cited).
3. **Independent reproduction**: wrote 6 fresh `by rfl`/`rfl` probes in my clone
   (mod=1 `[48,89,45]`, REX-75, LOCK `F0`, `0F 05`, truncated 9-byte movImm,
   `ret` suffix intact) — `./lean-probe`: **0 errors**. The audit's §4 extra
   pins all hold; no invented bug, no false refusal claim.
4. **Build evidence**: `BUILD-EVIDENCE.json` is internally consistent — pinned
   head `46a19a18` matches the commit output, base `0b3132b7` matches the log,
   file listing matches the PATCH, `./lean-bau` 392 jobs green, probes 0 errors.
   The honest `commit.sh`-without-`git-add` failure followed by the successful
   retry is recorded, not hidden. Nothing forged.

## Defects

None material. Two sub-line nits for the author (no repair required):
- §2 "opcode 139 with mod=3 falls through to `none`" fires in `decodeRegReg`'s
  catch-all, not literally at L365-372.
- `Bild.lean` L530-532 citation is off by ~2 lines against current HEAD.

## Verdict

The audit delivers exactly its bounded claim: an accurate, source-faithful,
correctly-scoped decode-boundary review with reproduced probes, honest CUTS
ledgering, and no overclaim toward hardware, source lowering, or validation
closure. P0-P3 assignments respect existing owners.

CANDIDATE: 406 46a19a189e533deff2184d5dacb58aae63239926
VERDICT: ACCEPT
