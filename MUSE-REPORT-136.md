# MUSE-REPORT-136 (lane 136, T1 part 1: certificate soundness for statements)

## What was built

New file `grammatik/Grammatik/ZeugnisStmt.lean` (1145 lines), imported at the
end of `grammatik/Grammatik.lean`. It extends `Zeugnis.lean` (expressions) to
statements, following that file's architecture exactly: plain-data
certificates, recomputed validity predicates with `Decidable` instances
(`decide`-closed acceptance and rejection), soundness by structural induction.

### New definitions

- `CertCond D` — bool conditions as plain data: `wahr`, `falsch`, `var`,
  `lt`, `le`, `eq`, `und`, `oder`, `nicht` (int comparisons over `CertExpr`).
- `CertStmt D V` — one statement as plain data (22 constructors).
- `CertSeq D V` — one `Block` as plain data (`nil`, `cons` with carried
  middle resource list `Λm`, `bind`, `bindCall`, `bindCallElse`, `regLies`,
  `regLiesElse`, `awaits`, `exchange`, `narrow`, `pruefung`).
- `CertEnd D V` — one `Endblock` as plain data (`ret`, `retWert`,
  `retGrund`, `leave`, `next`, `cons`, `bind`).
- `ctxBoolTyp`, `certCondGueltig`, `certStmtGueltig`, `certSeqGueltig`,
  `certEndGueltig` (validity Props), `decCondGueltig`, `decStmtGueltig`,
  `decSeqGueltig`, `decEndGueltig` + `instDecCond/Stmts/Seq/End` instances.
- `rankOk D L Λ : Bool` — the `locks` rank side recomputed as a fold over
  the finite `Λ` (the `∀ M` premise only fires for locks named in `Λ`).
- `certCondOk`, `certStmtOk`, `certSeqOk`, `certEndOk` — the `→ Bool`
  checkers (`decide` of validity).
- `refCertEin` — the printed certificate of `refP`'s `einzahlen` body.

### New theorems (all premises used; no `sorry`/`axiom`/`admit`)

- `ctxBoolTyp_var`, `rankOk_true`, `cond_sound`, `stmt_sound`,
  `seq_sound`, `end_sound` (mutual).
- **Target** `zeugnisStmt_sound (D) (V) (l) (Γ) (Λ) (c)
  (h : certEndOk … = true) : ∃ _ : Endblock D V l Γ Λ, True`.
- **Witness** `zeugnisStmt_sound_zeuge`: instantiates all premises jointly
  (`refD`, `vertragVon refD refEin`, `false`, `[.int 0 10]`, `[held]`,
  `refCertEin`, acceptance by `decide`) plus the non-degenerate run
  (`MB`, `refB_erreicht`, `refB_schreibt`: table `konto` written, 4 reached
  steps, slot `0 → 100`).
- Acceptance probe (`certEndOk … refCertEin = true` by `decide`),
  end-to-end elaboration example, two rejection probes (forged guard by
  `decide`, forged index shape `= false` by `decide`).

`#print axioms` for all seven: only `[propext, Classical.choice,
Quot.sound]` — the project's standard base, no extra axioms.

## Coverage: 38 of 49 constructors

Covered — Stmt (21/26): assignSlot, assignVar, assignGlob, schreibBytes,
uebergang, ite, onOption (`some`-introducers only), call (nullary only),
locks, breaking, traverse, retry, forever, publish, regSchreib, advances,
retires, ret, retWert, retGrund, leave, next. Block (11/17): nil, cons,
bind, bindCall (nullary), bindCallElse, regLies, regLiesElse, awaits,
exchange, narrow, pruefung. Endblock (6/6). CertCond (9/9).
Booked with reasons in `CUTS`: assignDurch/callInd/bindCallInd (pointer
exprs carry no range), onTag/onGrund (need `Arms`/`GrundArms` list
elaboration), axiomCall/bindAxiom (foreign-write/guard frames quantify over
arbitrary carriers — travel as proofs only in indexed certificates),
transition (no `DecidableEq D.Reg`), gleit×4 (need float rows), plus the
inherited expression bookings. Restrictions R-1..R-3 documented in-file.

## Rust side (task question 4)

`crates/gabbro-check/src/certemit.rs` prints EXPRESSION certificates only;
`zeugnis.rs` is the A/B/C/D translation census, not a derivation printer.
So: the Rust side prints nothing for statements today. The print format the
transfer phase must emit is designed in the `CUTS` block: per
statement/block the `CertStmt`/`CertSeq`/`CertEnd` term in `CertExpr` print
syntax, the claimed resource flow (`Λ`/`Λm`/output as names), and the
recomputed side lines (`darf`/`gdarf`, `V.schreibt`, rank order, index
shape, `Perm` balance); `RufPasst` travels as a checked reference.

## Last build

`./lean-bau` → `== 0 error line(s) in the COMPLETE output`
(`✔ [89/90] Built Grammatik`, `Build completed successfully (90 jobs)`).

## What remains open

The 11 booked constructors above; wiring `cut3_sound`/`CertCut4` to pinned
types for option/sum/pointer scrutinees; the Rust statement printer; the
closing per-program theorem (with T2–T4).

## Task feedback (rule 4/12)

Nothing in the task was weakened: `zeugnisStmt_sound` has no added
premises and the conclusion is the asked soundness form. One precision
note: "elaborating to the actual body term" holds in the sense the
soundness yields `∃ _ : Endblock … [.int 0 10] [held]` — EXACTLY
`refRumpfEin`'s type, with `refRumpfEin` as the reference inhabitant —
not as a proved term equality (the proof uses choice internally, so the
witness term is not computational). If the transfer phase needs a
computational elaborator (`Option`-returning with `rfl` equality to the
body), that is a separate, small definition over the same validity
predicates.
