# Opus agent report: closing theorem stage (a), generic (2026-09-15)

*Final report of the Opus agent, handed over from the laptop session for the merge on the
server. Branch base: master 282a45f1. On fisch: full `lake build` (236 jobs), `cargo test
--no-fail-fast` and `./instrumente/pruefe-emission.sh` green. No `sorry`, `native_decide` or
new `axiom`.*

**Chain count: 1 of 101 -> 2 of 111** -- `beispiele/104` and `beispiele/108`, each closed by a
Lean-checked instance of the generic theorem.

**The theorem.** `schlusssatz (K : Kette src) O hH orc XR hXR bin tief hA1 sp init hA4`
(`grammatik/Grammatik/Schlusssatz.lean`).
- `Kette src` holds only Lean propositions and data: the parse result `uebersetzeAllg src = .ok
  ⟨u, E.P, fs0⟩` (one generic pipeline: lex, parse, lane-162 preprocessing, elaborate, generic
  `lowerAllg`); `E : Einheit (declOf u)`; `akzeptiert_pruefer.akzeptiert E … = true`;
  `NutzerPflicht E`; the emitter's layout, the certificate `zert`, `korrOk … = true`.
- Named hypotheses about the world outside Lean: `hH : HardwareAnnahmen O E.Q`; `hXR :
  XR.Funktional` (foreign calls deterministic); `hA1` (every run of the binary's `f` is a
  `CallAt` run of `kProg K.zert` at depth `tief f` -- A1 with A2 and A3); `hA4 : EinFadenStart`
  (A4 single-threaded).
- Six parts, generic: parse fidelity; the checker Bool + `AkzeptiertSpec` + `korrOk`;
  `NutzerPflicht`; every C run (if the Gabbro call ends without a model error, the C call has a
  run and every run ends related); the machine (`rufAt_mitRuhe` replacing the hand `gPB`,
  `einfaden_ziel` via `ziel_ort_einfaden_ende` on `E.P.mitRuhe`, `gabbro_ziel` for the declared
  starts); every run of the binary.

**T2 proper.** `korrOk` (`KorrespondenzAllg.lean`) replaces `certOkG`: one decidable check
walking each body with its rows; covers pointer and named-table stores, local stores, calls
with arguments, `let`, `(void)x`, return and fall-off, literal/variable/widening/slot-load/
table-pointer expressions; anything else -> `false`. Sound at every depth (`korrOk_fnCorr`, new
lemma `argsTo_of`); `korrOk_faellt` refuses four planted defects.

**Instances.** `schlusssatz_104` unchanged beside it. 104: `Kette104.lean`, `Kette104Satz.lean`
(real text with comments, byte-identical; `kette_104_zeuge` slot 0 -> 100 in Gabbro and every C
run). 108: `Kette108.lean` (two declared concurrent starts accepted; `kette_108_zeuge` reads 42;
`kette_108_nebenlaeufig`). Witnesses `einfaden_ziel_zeuge`, `korrOk_zeuge` in
`SchlusssatzZeuge.lean`. Axioms: propext, Classical.choice, Quot.sound only.

**Rust.** `corrlean.rs`: third printed section `KCert` with the exporter's map; named-table
loads/stores print as rows; three new tests. `zaehle-kette.py` counts a chain only with a
`CHAIN-INSTANCE` marker, byte-identical source, text-identical pasted certificate, a file
applying `schlusssatz <name>`, and (with `--lean`) a green build; column (a) measured for every
program by evaluating `uebersetzeAllg`. `pruefe-cformen.py`: `(void)f(a)` no longer read as the
argument list (10 `expr:call` occurrences leave "without semantics"); the hand quote in
`CFormenZeuge.lean` is stale in spelling, not meaning.

**Where the other 109 stop:** all at sieve (a): 20 at the parser (10 `reserved head forall`),
89 at elaboration (69 item without G form, 12 unit without a table, 7 `bool`, 1 `requires`).
Next gains need T3 parser/elaborator widening.

**Open (plan §6.5, SATZKARTE §27):** `korrOk` lacks `if`, `traverse`, compound assignment,
globals, `let` of a call, arithmetic; part 4 conditional on no model error; the `Einheit`'s
invariants/ensures/starts/initial memory are written by the chain's author, not the exporter
(lane 198); A2 and non-Lean parts of A1/A3/A4 outside Lean; single-thread machine <-> `rufAt`
link not re-instantiated.

**Merge note.** Master moved (muse-195); `Grammatik.lean` imports may conflict trivially.
**Both stage (a) and stage (b) added a SATZKARTE §26**; at the merge on the server stage (a) became **§27**, stage (b) kept §26.
