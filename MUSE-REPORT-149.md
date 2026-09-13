# MUSE-REPORT-149 (lane 149: term identity for expression certificates)

## What was built

New file `grammatik/Grammatik/ZeugnisIdent.lean` (975 lines), imported at the
end of `grammatik/Grammatik.lean`. It closes the Lean half of lane 146's
"Term identity" gap (MUSE-REPORT-146.md): nothing proved the printed
certificate describes the SAME term the checker checked (`certemit.rs` books
"printer-prints-what-was-checked is trust base there").

### New definitions

- `varIdx : Var Γ τ → Nat` — de Bruijn index a `CertExpr.var` names.
- `varOfAll : (Γ : Ctx) → Nat → Option (Σ τ, Var Γ τ)` — computational
  inverse of `varIdx` at any type; bounds read from the context, never
  trusted from a print.
- `varOf : (Γ : Ctx) → Nat → Option (Σ lo hi : Int, Var Γ (.int lo hi))` —
  int-typed projection (the shape `elabInt` uses).
- `printInt : Expr D Γ Λ τ → Option (CertExpr D)` — Lean-side printer from
  the CHECKED (typed) term; proof fields forgotten, recomputed by `elabInt`.
  The 17 `CertExpr` shapes print; the 23 shapes with no `CertExpr` print
  (`durch`, `altGlob`/`altSlot`, `leseBytes`, every non-`int` constructor)
  answer `none` — booked, not faked, one explicit arm each.
- `elabInt : CertExpr D → Option (Σ τ, Expr D Γ Λ τ)` — computational
  elaborator (Option-returning, no choice inside): every side condition
  `certRange` recomputes is rechecked with `if` (integer order/equations
  from the core, `darf`/`gdarf` from `Zeugnis.lean`); proofs rebuilt.
  Result type read off the certificate, never supplied.

### New theorems (all premises used; no `sorry`/`axiom`/`admit`)

- `varOfAll_varIdx`, `varOf_varIdx` — variable roundtrips.
- `varOfAll_ctxTyp` — a rebuilt variable reads back through `ctxTyp`
  (links elaboration to the existing range table).
- `print_elab_all` — print-then-elab round-trips to the SAME term, by
  induction over every `Expr` constructor (40 arms: 17 round-trip, 23 state
  `True` on the none-branch). Proof irrelevance absorbs rebuilt proofs.
- `print_elab` — the task's proposed shape at int type
  (`elab (print e) = some e` where print is defined), exact corollary of
  `print_elab_all`.
- `elab_valid` — converse: `elabInt c = some ⟨.int lo hi, e⟩` implies
  `GueltigAbleitung D Γ Λ c lo hi`; with `zeugnis_sound` this yields both
  validity and the judgment. Induction over the certificate, deterministic
  `cases`+`obtain` template (no `split` naming fragility), single-level
  type casing with multi-pattern catch-alls.
- Witnesses (rule 13), all on `refD`/`refP` with `refHundert`/`refReqEin`
  and the fixture write (`refEin_schreibt`: `einzahlen` writes `konto`):
  `print_elab_all_zeuge` (some-branch and none-branch),
  `print_elab_zeuge`, `elab_valid_zeuge` (premise by `rfl` computation,
  validity by `decide`).

`#print axioms` for all six mains + witnesses: only
`[propext, Classical.choice, Quot.sound]` — the project standard base.

## Last builds

- `./lean-probe grammatik/Grammatik/ZeugnisIdent.lean` → `== 0 error(s)`.
- `./lean-bau` → `== 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (113 jobs)` (`[111/113] Built
  Grammatik.ZeugnisIdent`).

## What remains open (in-file `CUTS`)

- Certificate rows for `durch`/`altGlob`/`altSlot`/`leseBytes` and the
  CUT-3 bool/float/option/sum/ground/quantifier/`reaches` rows have no
  `printInt`/`elabInt` direction yet (same remainder as `Zeugnis.lean`).
- Rust residue = trust base left (for the transfer lane): `certemit.rs`
  must print `printInt e` for the CHECKED `e` (typed term, not raw AST),
  and its `cert_range` must agree with `certRange` on every arm. Measured
  gaps today: `sub`/`neg`/`mul`/`rem`/`sdiv`/`srem` have Lean print arms
  but no Rust `CertExpr` variants at all; Rust `Shl`/`Shr` carry no width
  while `CertExpr.shl/shr` (and `Expr.shl/shr`) do. Until the Rust print
  equals `printInt e`, the Lean statement does not apply to its output.

## Task feedback (rules 4/12/13)

- The proposed `theorem print_elab (e : CheckedExpr) : elab (print e) =
  some e` assumes a total printer and a `CheckedExpr` type; neither exists
  (23 `Expr` shapes have no `CertExpr` print). I kept the name `print_elab`
  with the match-form statement (round-trip exactly where print is
  defined, `True` elsewhere) — an elaboration detail, not a weakening:
  for every printable constructor it says `elab (print e) = some e`.
- "For EVERY expression constructor covered by Zeugnis.lean (by
  induction)": I cover all 40 `Expr` constructors by induction, which is
  more than the `CertExpr` fragment (the CUT-3/CUT-4 certificate shapes
  cover further judgments existentially/conditionally; their print
  direction is the booked remainder above, not silently included).
- No rule-13 witness quantifies anything away: witnesses exhibit concrete
  `refD` terms and prove the instantiated statements plus the fixture
  write. No codes, gifts, or examples were needed (none reserved).
- Two proof-engineering findings, for later lanes: (1) `cases h :
  elabInt a` elaborates the discriminant with fresh metavariables for
  `Γ Λ` (`CertExpr` mentions only `D`) — implicits must be pinned
  explicitly; (2) an `obtain`-substituted `dite` proof leaves a stuck
  `And.rec` that `rfl` cannot close — projection casts (`Eq.mp` over
  `congrArg`) reduce cleanly instead.
