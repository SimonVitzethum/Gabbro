# MUSE-REPORT-300: Independent review of candidate 284 (byte-granularity x86-TSO)

Lane 300, reviewer. Model: opencode-go/muse-spark-1.3-contributor, no delegation.
Isolation: pwd /home/simon/Dokumente/gabbro-muse/a300, branch muse/300 (checked first).
Reviewed ONLY the pinned snapshot in `.tmp/review/` (SNAPSHOT.json author 284,
HEAD e308f0637a0855a2b66f4e818a30f2ae6f7e935e, base dd02d9120be5540dc3773affcc4c647c4bae940b,
files MUSE-REPORT-284.md, grammatik/Grammatik.lean, grammatik/Grammatik/X86/TSO.lean)
plus BUILD-EVIDENCE.json and OWNER-TASK.md. No other clone read, no code edits;
own file is this report only.

## What was checked

- Snapshot file `grammatik/Grammatik/X86/TSO.lean` (622 lines) read in full:
  definitions (`TSOEintrag`, `TSOZustand`, `pufferSetze`, `issueByte`,
  `neuestens`, `loadByte`, `flushKern`, `zaunBereit`, `TSOSchritt`,
  `TSOErreichbar`, `Ausgerichtet`, `paketAtomarMoeglich`, `LockSchritt`,
  `tsoEineHist`, `sbX/sbY/sbEins/sbStart/sbNach1/sbNach2/sbGespült`)
  and all theorem statements AND proofs, plus CUTS block and 39 `#print axioms`.
- PATCH.diff: exactly 3 files (report, one additive `import Grammatik.X86.TSO`
  in Grammatik.lean, new TSO.lean). No Typen/Speicher/goal/Spec edits, no Rust,
  no diagnostic/gift/example/CLI numbers, no MARKE_EMIT. Scope-clean.
- Forbidden terms: `grep` for sorry/admit/axiom-decl/native_decide/unsafe (outside
  `#print axioms` lines) finds nothing. No `intro _` / `have _ :=` discards
  (`intro h` at line 482 is consumed by `cases h`; `intro m hm` at 546 both used).
  No `Prop`-typed premise; spot-checked every premise is used
  (e.g. `load_nach_issue` uses h+hrd, `paket_reisst` uses hne via Ne.symm,
  `flush_schreibt_kopf` uses h/e/rest/he).
- No quantification over source syntax (`Vertrag/Stmt/Endblock/Expr`): no `_zeuge`
  obligation arises. Concrete reached memory-changing witness present instead.
- Canonical-memory claim: `TSOZustand.mem : Speicher` reuses `Grammatik.X86.Typen`
  `Speicher` (bytes/lesbar/schreibbar/ausfuehrbar over `Adresse := BitVec 64`,
  `Byte := BitVec 8`); `zeugenSpeicher` matches canonical witness in
  Speicher.lean (zeroed, fully permissive). Not a second memory model.
- State-changing semantics (rule 4c): `flushKern` writes
  `bytes := fun x => if x = e.addr then e.wert else ...`; `flush_schreibt_kopf`,
  `flush_rahmen`, `sb_flush_aendert_speicher` prove observable canonical change.
  Loads/fences correctly change no state and are (correctly) no steps.
- FIFO/forwarding correctness: `neuestens` recurses youngest-first over an
  oldest-first list (LAST match wins) — correct; `neuestens_angehaengt`,
  `load_nach_issue`, `fifo_reihenfolge` generic over all l/s/a/v. No
  name/example-specific rule; witness names (sbX/sbY) appear only in witness defs.
- Fence locality: `zaunBereit_iff_leer`, `zaun_nach_flush`, `zaun_fremd_issue/_flush`
  plus `zaun_kein_fremd_drain` (core 0 ready while core 1 holds a store) — the task's
  "do not pretend a local fence drains foreign buffers" is proved, not assumed.
- Packet/LOCK scope honest: `paket_ein_byte` + `einzelbyte_atomar` (width 1 atomic by
  construction), `paket_reisst` proves two-byte tear (no multi-byte atomicity even
  aligned), `LockSchritt` empty + `kein_lock_schritt` (no LOCK transition, OPEN in
  CUTS). Compliant with "proved packet rule OR refused+OPEN".
- View link: `tso_last_lesbar` embeds each `loadByte` result in a per-load singleton
  history as `Lesbar` at `(Adresse, Byte)`; `tso_frisch_beispiel` inhabits `Frisch`.
  Mathematically true but weak (any value is Lesbar in its own singleton) — author
  labels it target-side only with NO carrier mapping and records the real
  cross-granularity refinement as OPEN in CUTS. Not oversold; no assumed simulation.
- Edge details: `paketAtomarMoeglich` guards `0 < n` so `a.toNat % n` never divides
  by zero; `sbX_ne_sbY` by decide; issue checks `schreibbar`, load checks `lesbar`;
  flush needs no recheck because permissions are proven immutable
  (`issue/flush_erhaelt_berechtigungen`). `decide` used is kernel-checked, not
  `native_decide`.
- Report cross-check: "~640 lines" (actual 622), import claim, "nothing else touched",
  axiom claim (nothing or [propext]), witness equations by rfl/decide, and the 3 OPEN
  items all match the code and CUTS. BUILD-EVIDENCE log is honest (shows intermediate
  red probes fixed during development, final green).

## Independent build evidence (queued wrapper only, no lake/lean directly)

- `./lean-probe .tmp/review/author-284/grammatik/Grammatik/X86/TSO.lean`:
  `== 0 error(s) in the COMPLETE output`, followed by all 39 `#print axioms` lines,
  each `does not depend on any axioms` or `depends on axioms: [propext]` — subset of
  the standard set, no Classical.choice/Quot.sound needed. Matches the report's claim.
- Full `./lean-bau` deliberately NOT rerun here: the candidate file lives only in the
  `.tmp` snapshot, not in this clone's `grammatik/`, so a local full build would not
  exercise it; the per-file probe with project imports plus BUILD-EVIDENCE's recorded
  final `./lean-bau` (`exit 0, 0 error lines, 369 jobs`) is the evidence pair.
- Counterexample reproduction: none needed — no finding reproduced a false theorem;
  every checked `decide`/`rfl` claim is green in the probe.

## Findings

None material. Two non-blocking notes for the merger (not candidate defects):
1. Snapshot base dd02d912 predates this clone's HEAD (62eb70f3); Grammatik.lean needs
   the standard import-union merge (current tree has 3 extra Folge imports).
2. `tso_last_lesbar` is a deliberately weak target-side embedding; its value is the
   honest OPEN obligation next to it, not the embedding itself.

CANDIDATE: 284 e308f0637a0855a2b66f4e818a30f2ae6f7e935e
VERDICT: ACCEPT
