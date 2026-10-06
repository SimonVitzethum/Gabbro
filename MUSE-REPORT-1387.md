# MUSE-REPORT-1387: GabbroV bridge — StartPflicht without the Initially assumption

Lane 1387, clone `/home/simon/Dokumente/gabbro-muse/a1387`, branch `muse/1387`.
Status: **BLOCKED before any machine check. No Lean statement of this lane has been
verified. Nothing Lean is committed.** This report is the committed artifact.

## 1. What was done (reading only — all verified by inspection)

- Read the goal premise (b): `StartPflicht E` (`sperren`: every lock invariant at
  `E.sp0`; `req`: every declared start's `requires` at `(E.sp0.welt [])` with its
  declared arguments) and `Einheit` (`P`, `S`, `Q`, `starts`, `sp0`, `gestartet`)
  in `grammatik/Grammatik/Zielsatz/Kern/Spec.lean` (lines 1509–1515, 1665–1673).
- Read `messung/GABBROV-BRUECKE-REPORT.md` fully (S0–S6): the bridge is closed for
  2 of 146 units (104, 108); `Start.lean` discharges `StartPflicht` only from the
  lowering SHAPE (`requires := .wahr`, empty lock family), never from a duty at an
  initial memory.
- Read GabbroV's `Initially`: `Initially s0 := wellFormed s0 := WF shapeOf s0.world`
  (`programmlogik/Duty/Duty104Referenz.lean` lines 67–71;
  `programmlogik/Gabbro/Body.lean` line 1126). Not edited (lane has no mathlib cache).
- Established the exact source of initial memory on both sides:
  - Lean parser fragment: `declOf u` has `Glob := Empty`
    (`grammatik/Grammatik/Parser/UebersetzeAllg.lean` line 156) — the fragment
    elaborates NO statics. Slots are the only initial memory there.
  - Rust exporter: `gSp0` (slots at zero: `false`/`⟨0,…⟩`/case 0; globals at their
    DECLARED initialiser via `GInit`: `Int`/`Bool`/`Sum`) and the `check_sp0`
    refusal (zero/initialiser outside the range has no `sp0` form)
    (`crates/gabbro-check/src/lean_g.rs` lines 456–466, 1958–2074, 3727–3755,
    5848–5915).
- Established the witness reuse path (all accepted, in-`grammatik`):
  `uExp104` (table `Konto` count 2 = array, writer `einzahlen`,
  range `(0,100)` holding 0) in `Parser/Uebersetze.lean` line 2237;
  `Kette104.low4 : lowerAllg uExp104 = .ok (P4, fs4)`,
  `Kette104.P4/fs4` in `Korrespondenz/Kette/Kette104.lean` lines 37–51.
- Confirmed every helper lemma name in-tree before use:
  `List.getElem?_eq_getElem`, `List.getElem_mem`, `List.mem_of_getElem?`,
  `List.all_eq_true`, `rangeO_some` (`UebersetzeAllg.lean` line 251),
  `sperrInvOk_leer`, `axWahr` (`Zielsatz/ZielOrt/Rahmen/ZielOrtRahmenBeweis.lean`
  line 70), `Val.int_bereich`, `Expr.wahr`/`eval`/`wahr?` reduction
  (`eval σ₀ .wahr σ ρ = true`, `wahr? true = true`, both `rfl`).
- Wrote the skeleton draft `grammatik/Grammatik/X86/GvStartPflicht.lean`
  (48 lines, imports + `Sp0Ok`; still UNTRACKED in the working tree, NOT committed).
  `grammatik/Grammatik.lean` is untouched (no import line added — nothing is green).

## 2. Concrete obstruction (why nothing is machine-checked)

`./lean-probe` is the only allowed Lean check. It routes through the shared
single-slot wrapper `lean-slot` and captures ALL output until the process ends,
so it prints nothing until the slot grants execution AND the import closure
elaborates. Four invocations across two turns — ~10, ~58, ~20 and ~30 minutes
(about 2 hours total) — produced **zero output bytes**: no `== N error(s)` first
line, no diagnostics. Per rule 2 no other check (`lake`/`lean` direct) is allowed;
process inspection (`ps`) and detached execution (`nohup … &`) are denied to this
lane, so queue-wait versus stale-cache rebuild cannot be distinguished from here.
Repeating the probe a fifth time is repeating, not diagnosing — hence this report
instead of another blind run. Next step for whoever resumes: single `./lean-probe`
on the unchanged skeleton when the slot is known-free; only then proceed below.

## 3. Implementation plan (not yet executed — names and statements fixed)

In `grammatik/Grammatik/X86/GvStartPflicht.lean`
(namespace `Gabbro.Grammatik.X86`), reusing accepted definitions unchanged:

1. `Sp0Ok (u : UProg) : Prop` — every field of every table is a `bool` field or
   an integer field whose recorded range holds `0` (DRAFTED, unverified).
2. `sp0OkB (u : UProg) : Bool` — `u.tabellen.all` over
   `felder.all (fun (name,(lo,hi)) => bools.contains name || decide (lo ≤ 0 ∧ 0 ≤ hi))`.
3. `sp0OkB_klingt : sp0OkB u = true → Sp0Ok u` — via `List.all_eq_true`,
   `List.mem_of_getElem?`, `List.getElem?_eq_getElem`, `rangeO_some`.
4. `sp0FeldWert` / `sp0Of (u) (h : Sp0Ok u) : Speicher (declOf u)` — slots at
   zero (`false` / `⟨0, _, _⟩`), `globs := fun e => nomatch e`; unfold `typAt`,
   split on `boolFeldAt`, rewrite the `fieldRangeO` arm.
5. `gv_lowerAllg_requires` — `lowerAllg u = .ok (P, fs) → ∀ f, P.requires f = Expr.wahr`
   (mirror of the accepted `bruecke` S4 lemma over the same `progOfFn` definition;
   no interpreter duplicated), then `gv_startPflicht`:
   lowering-ok + `Sp0Ok` + starts ⇒ `StartPflicht ⟨P, leer, axWahr, starts, sp0Of, []⟩`
   (`sperren` by `rfl` on `SperrInv.leer`; `req` by unfold + `rfl` on `.wahr`).
6. `gvInitWert` (mirror of `GInit`: `int`/`bool`/`sum` over `Ty`) with
   `gvInitWert_int_ok` (in-range initialiser travels, value `.n` is the numeral)
   and `gvInitWert_int_none` (out-of-range is `none`: the `check_sp0` refusal).
7. Obstructions, proved: `sp0_luecke` (non-bool field whose range misses zero ⇒
   every memory has a nonzero slot there, via `Val.int_bereich`);
   `gv_fragment_kein_static : (declOf u).Glob = Empty` (`rfl` — any `static` is
   outside the fragment, needs the exporter `gD` world + `gvInitWert`).
8. `gv_startPflicht_zeuge` — joint witness on `uExp104`/`Kette104.low4`:
   `Sp0Ok` by `sp0OkB_klingt` + `decide`, `count = 2` (array),
   `writesAt` true for `einzahlen` (non-degenerate: table + writer),
   non-zero static initialiser `gvInitWert … (.int 0 100) (.int 64) = some …`.
9. `CUTS:` block + `#print axioms` for each main theorem (standard axioms only);
   one `import Grammatik.X86.GvStartPflicht` line at the end of
   `grammatik/Grammatik.lean`; full `./lean-bau` before any commit of Lean work.

## 4. What remains open

Everything executable: no `./lean-probe` line and no `./lean-bau` line were ever
produced by this lane. The draft file is unchecked-in and uncommitted by design
(rule 8: never commit an unverified build).

## 5. Things in the task I believe are wrong or imprecise

- "Non-degenerate witness: a unit with a non-zero static initialiser and an
  array": the parser's fragment CANNOT spell a `static` (`Glob := Empty` in
  `declOf`), so no single fragment unit carries both. The honest witness pairs
  the fragment's array unit (`uExp104`, `Konto` count 2 + writer) with the
  exporter-side static model (`gvInitWert` with initialiser 64). This is a
  task-shape finding, not a weakening: section 3 item 8 implements exactly this.
- The owned-files list names `MUSE-REPORT-1387.md` twice (harmless duplication).

## 6. CUTS (of this report — the lane's work, not a proof)

- PROVED: nothing (no machine check completed).
- STATED with evidence: the reading findings of section 1 (file:line pins).
- DESIGNED but unexecuted: the definitions/theorems of section 3.
- OPEN: every executable step; the `Initially`-follows-from-declarations theorem;
  the exact obstruction classes as machine-checked proofs.
- `#print axioms`: never run (no build completed).
