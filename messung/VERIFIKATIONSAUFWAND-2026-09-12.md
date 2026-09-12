# Verification effort estimate for Gabbro itself — 2026-09-12 (lane 127)

Analysis lane: no code changes. "Formal verification of Gabbro" = the
implementation (Rust checker `crates/gabbro-check`, parser
`crates/gabbro-syntax`, C emitter `emit.rs`) is PROVED to implement the Lean
model under `grammatik/`: checker soundness, emitter correctness (emitted C
refines the model's semantics, up to named C-compiler and hardware
assumptions), plus whatever of the Lean model is still open
(`dokumente/SATZKARTE.md` §§7–10). Assumed growth before verification is
done: **+30%** on today's codebase.

All numbers below were measured on 2026-09-12 on the build server. Commands
are given so any lane can re-run them.

## 1. Today: code, proofs, and existing verification assets

### 1.1 Measurement commands

```bash
wc -l crates/gabbro-check/src/*.rs crates/gabbro-syntax/src/*.rs crates/gabbro-cli/src/*.rs
wc -l grammatik/Grammatik/*.lean | tail -3
find programmlogik -name '*.lean' | xargs wc -l | tail -3
wc -l beweise/*.thy | tail -3
grep -rh --include='*.lean' -E '^(theorem|lemma) ' grammatik/Grammatik/ | wc -l
grep -rh --include='*.thy' -E '^(theorem|lemma) ' beweise/ | wc -l
git log --since '2026-08-01' --numstat --pretty='COMMIT%x00' -- grammatik/ beweise/ \
  | awk '/^[0-9]+\t[0-9]+\t/{split($0,f,"\t"); a+=f[1]; d+=f[2]} END{print "added="a" deleted="d" net="a-d}'
```

### 1.2 Rust implementation (lines)

| Crate / file | Lines | Note |
|---|---|---|
| `crates/gabbro-check` total | **76,250** (49 files) | the checker |
| `emit.rs` | **14,415** | the C emitter, single file |
| `m1.rs` | 7,117 | range/type lattice |
| `lean.rs` | 6,832 | Lean export (`gabbro lean`, channel B) |
| `namen.rs` | 5,064 | |
| `saetze.rs` | 3,940 | |
| `domaene.rs` | 2,597 | |
| `geteilt.rs` | 2,476 | |
| `umgebung.rs` | 2,016 | |
| `kosten.rs` | 1,713 | |
| `paarung.rs` | 1,648 | |
| `m3.rs` | 1,476 | |
| `zeugnis.rs` | 1,318 | certificate producer (Rust side) |
| `certemit.rs` | 872 | certificate emission |
| `ableitung.rs` | 855 | derivation builder |
| `corrcert.rs` | 541 | correspondence certificate |
| remaining 35 files | ~14,370 | |
| `crates/gabbro-syntax` total | **8,861** (7 files) | parser; `parse.rs` 5,400, `ast.rs` 2,124 |
| `crates/gabbro-cli` total | **3,523** (4 files) | CLI, build gate |
| **Rust total** | **≈ 88,600** | **+30% → ≈ 115,000** |

### 1.3 Proofs today

| Corpus | Lines | Files | Theorems/lemmas |
|---|---|---|---|
| `grammatik/` (Lean 4.33.1, no mathlib) | **53,076** | 60 | **1,552** `theorem`/`lemma` |
| `programmlogik/` (needs mathlib, out of scope to build) | 10,066 | — | — |
| `beweise/` (Isabelle) | 3,512 | 15 `.thy` | 24 `theorem`/`lemma` |

No `sorry`/`axiom` in `grammatik/` (only the words in comments); the goal
family rests on `[propext, Classical.choice, Quot.sound]` (SATZKARTE §9).

### 1.4 Existing verification assets (what is already certificate-shaped)

| Asset | Size | State |
|---|---|---|
| `grammatik/Grammatik/Zeugnis.lean` | 1,696 lines, 39 decls | `CertExpr` plain-data certificates, `certRange` table recomputed in Lean, `zeugnis_sound` (valid certificate implies the `Expr` judgment) |
| `grammatik/Grammatik/Erhaltung.lean` | 976 lines, 82 decls | correspondence as data (`CorrSite`/`CorrCert`), alias obligation (census: 491 pointer-arithmetic sites), cost claim, ruling table with priced statuses, table CLOSED (`tafel_geschlossen`); per-slot semantic adequacy stays cut |
| `zeugnis.rs` + `ableitung.rs` + `certemit.rs` + `corrcert.rs` | 3,586 Rust lines | producer side of the certificate pair |
| `lean.rs` export | 6,832 Rust lines | tree → `Gabbro.Body` datum (PLAN-VERIFIKATION §3: fidelity unproved, witness-pairs proposed) |
| `beweise/` ghost-theory templates | 3,512 Isabelle lines, 24 theorems | 4 of ~20 template obligations machine-checked (BEWEIS.md L3) |
| C-form census (`zaehle-c-formen.py`, 2026-08-31) | 64 forms over 8,001 lines C | **34** allowed+used, **30** used-but-undecided (7 contradict the never-list, incl. pointer arithmetic at 491 sites) |

Intended architecture (BEWEIS.md, PLAN-VERIFIKATION.md, PLAN-UMSETZUNG.md):
**translation validation** — the checker prints derivations/certificates per
program, Lean re-checks them (`gabbro-ableitung`, §1.3 print-and-typecheck;
`checker_agrees` witness pairs) — instead of verifying the Rust code
directly. Only §§1.3/U1–U8 of PLAN-UMSETZUNG are binding; nothing there is
built yet beyond the assets above.

### 1.5 What of the Lean model is still open (SATZKARTE §§7–10)

11 open duty items: **D1–D9, D11–D12**. Of these D2/D7 are pure
checker-computation duties (decidable per program, no new mathematics),
D1/D4/D5/D11 are run/witness wiring with a merged fragment each already
closed, and D3/D6/D8/D9/D12 need new theorems. Wave-4 lanes 80 (oracle
events) and 84 (adequacy of F, straight-line) are expected to close
D8/D12 and the straight-line halves of D5/D1.

## 2. Proof lines needed, per component, for both strategies

### Ratios used (all from memory — approximate, stated as such)

| Source (from memory) | Code | Proof | Ratio proof:code |
|---|---|---|---|
| CompCert (Leroy) | ~15k lines compiler | ~100k lines Coq | **≈ 6–7 : 1** |
| seL4 (Klein et al.) | ~10k lines C (sequential core) | ~200k lines Isabelle, ~20–25 person-years | **≈ 20 : 1** |
| CakeML (verified ML compiler) | ~10–15k lines compiler | ~100k+ lines HOL4 | **≈ 5–8 : 1** (from memory) |
| Vellvm (LLVM semantics + passes) | small pass code | large semantics + metatheory | **≈ 5–10 : 1** (from memory) |
| Gabbro's OWN ratio so far | model of a ~88k-line system | 53k Lean lines, 1,552 theorems (~34 lines/theorem) | model only, not verification; per-feature cost ~300–600 Lean lines per lane-task (measured: Trennung ~300, RelySperre ~600, VertragsFuss ~150) |

Strategy B uses CompCert's 6:1 for sequential checker/parser code, seL4's
20:1 as the ceiling for concurrent/sharing code, and a higher band for the
emitter (no C semantics exists yet — it must be built first).

### Strategy A — translation validation / certificate checking

Only the certificate checker and the model need proofs; the 76k-line
checker itself is never verified, only its per-run output is re-checked.

| Component | Proof lines (new Lean) | Basis |
|---|---|---|
| Finish the model: 11 open items D1–D9/D11–D12 | 6,000–10,000 | own ratio: 9 small items × ~500 + N-thread wiring D4 ~2,000 (largest single item) |
| Per-constructor certificate soundness (all `Stmt`/`Expr` constructors; `zeugnis_sound` covers `Expr` only) | 5,000–8,000 | ~40 constructors × 100–200 lines each |
| Correspondence rechecker + 30 open C-form rulings | 4,000–6,000 | 30 slots × ~200 lines; BEWEIS.md §1a |
| Export fidelity (`lean.rs` 6.8k lines → witness pairs / back-translation, PLAN-VERIFIKATION V5) | 2,000–3,000 | second tool, not a proof of the export |
| Ghost-template library (remaining ~16 of 20) | 2,000–3,000 | 4 done in 3.5k Isabelle lines incl. scaffolding |
| **Strategy A total** | **≈ 20,000–30,000 (mid ≈ 25,000)** | |

### Strategy B — direct verification of the Rust code

Via Aeneas/hax extraction to Lean, or a Lean rewrite + extraction; assumes
+30% growth applied below.

| Component | Code (grown) | Ratio | Proof lines |
|---|---|---|---|
| Checker passes (excl. emitter), sequential logic | ~80,000 | 5 : 1 (CompCert) | ~400,000 |
| Sharing/concurrency discipline (`geteilt.rs`, locks, marks) | ~5,000 | 10–20 : 1 (seL4 corner) | 50,000–100,000 |
| Parser (`gabbro-syntax`) | ~11,500 | 3 : 1 (parsers are cheap to verify) | ~35,000 |
| C-subset semantics first (64 forms; does not exist) | — | — | 10,000–20,000 |
| Emitter vs C semantics (incl. 491 ptr-arith sites, volatile, `restrict`, inline asm) | ~18,700 | 8–12 : 1 | 150,000–220,000 |
| **Strategy B total** | **≈ 115,000** | blended ≈ 6 : 1 | **≈ 600,000–800,000 (mid ≈ 700,000)** |

Strategy B is ~25–30× strategy A in proof lines — the standard reason the
project chose translation validation (PLAN-UMSETZUNG §1.3).

## 3. Time: velocity from the commit history and projection

### Measured velocity

```bash
# net Lean lines by era: human era (until 2026-09-10) vs agent waves (since)
# human era: added=12,982  net=+12,698 over ~25 active days (2026-08-13–09-09)
# waves:     added=46,728  net=+44,060 over 3 days (2026-09-10–12), dozens of parallel lanes
# distinct commit dates since 08-01: 28; total commits: 1,874
```

| Era | Net Lean lines | Active time | Velocity |
|---|---|---|---|
| Human era (designer, incl. design) | +12,700 | ~25 active days | **≈ 500 lines / active day** (solo) |
| Agent waves (40+ parallel lanes) | +44,100 | 3 days wall-clock | **≈ 14,700 lines / wall day; ≈ 200–400 net lines / lane-day** |
| Theorems | 1,552 total | — | ~34 Lean lines per theorem |

Assumptions for projection: rework rate ~50% in the agent lanes (per task
brief; gross lane output is roughly twice what survives review), agent
waves available or not stated per band, 250 active days per person-year.

### Projection

| | Proof lines | With waves (40 lanes × ~200 net/day) | Solo (≈ 500/day) | Person-time |
|---|---|---|---|---|
| A low / mid / high | 20k / 25k / 30k | ~1 week / **~1–2 weeks** / ~2–3 weeks wall-clock (≈ 65/85/100 lane-tasks at ~300 lines each ≈ 2–3 waves) | ~2 / **~2–3** / ~3 calendar months | ~0.3–0.5 person-years |
| B low / mid / high | 600k / 700k / 800k | ~75 / **~90** / ~100 wave-days ≈ 1–2 calendar years of sustained 40-lane parallelism | ~5 / **~6** / ~7 person-years at designer velocity; seL4 calibration (≈ 20 py for 10k C) suggests up to **15–25 person-years** for the concurrent + C-semantics parts | **mid ≈ 20 person-years** |

The solo-designer and seL4 calibrations disagree by ~4× on strategy B
(6 vs 20+ person-years); the seL4 number is the safer anchor because the
emitter/C-semantics and memory-model work has no counterpart in the
project's own history, and designer velocity includes no verification of
concurrent or C-level code.

## 4. Cheap, expensive, and the single biggest risk

**Cheap (already certificate-shaped):** the range-table recheck
(`certRange`/`GueltigAbleitung`), the derivation print pipeline
(PLAN-UMSETZUNG §1.3), decidable per-program checks (D2 separation,
D7 footprint containment — computation, not mathematics), the
correspondence completeness/order legs, the syscall pairing shape
(`SyscallPaarung.lean`, lane 115).

**Expensive:** the C emitter against a C semantics (the 64-form subset has
no formal semantics; 30 of 64 emitted forms were never decided and 7
contradict the never-list — BEWEIS.md §1a); concurrency (memory model is
RC11-without-SC by decision, but the chain↔machine grain mismatch —
whole critical sections vs per-event worlds — is still open, D4; seL4
sidestepped concurrency, Gabbro cannot); N-thread chain wiring (D4);
ghost OS state for syscalls (a model, not a proof).

**Single biggest risk:** the C-semantics gap. Emitter correctness is
unformulable — not just unproved — until the actually-emitted C subset
(64 measured forms, including 491 pointer-arithmetic sites the design
claimed to never emit) has a mechanized semantics plus a UB inventory
(`restrict`, signed overflow, shift-by-width, volatile, inline asm) pinned
against named compiler options. That semantics is ~10–20k lines of new
formalization standing outside every existing asset, and every emitter
proof (both strategies) hangs on it. If the subset keeps drifting (a 103rd
program reviving a dead form), the semantics never closes.

## Bottom line

Mid estimate: **strategy A (translation validation, the planned path)
needs ≈ 25,000 new Lean lines — about 1–2 weeks of 40-lane agent waves,
or 2–3 solo months (≈ 0.3–0.5 person-years)** — on top of a model that is
53k lines / 1,552 theorems today with 11 known open items; **strategy B
(direct verification of the ≈ 115k-line grown Rust codebase) needs
≈ 700,000 proof lines — ≈ 20 person-years, i.e. 1–2 calendar years even
with massive sustained parallelism** — dominated by the emitter-vs-C
semantics, for which no semantics exists yet; that missing C semantics is
the single biggest risk of the whole verification.
