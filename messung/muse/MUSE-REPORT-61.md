# MUSE-REPORT-61: shift width typed in Lean (PLAN-BITS.md section 2)

Lane 61, branch `muse/61`. Task: type the shift amount `0 ..< w` in Lean,
propagate to all uses, prove `shl_weite_im_c_definiert` (C UB row
"shift by >= width" unreachable) and `shl_rust_lean_gleich` (Lean premise
= Rust check) in `grammatik/Grammatik/Schiebung.lean`.

Revision 2 (2026-09-12, after reviewer feedback): the first revision
claimed an explicit `Nat` width on the `Expr.shl`/`shr` constructors is
erased by the elaborator. That diagnosis was WRONG. The reviewer measured
in this clone that `| shl (w : Nat) (hw1 : h1 < 2 ^ w) ...` builds
`Syntax.lean` cleanly and `#check @Expr.shl` shows the full type. What I
had seen as "Function expected" was the ARITY change: every pattern
`.shl h0 h0' a b` and term `Expr.shl h0 h0' a b` needed three more
arguments. Correction: my failing variants had put the `w` binder in
positions (implicit `{}`, `where`-clause, trailing) that genuinely erase
or misplace it; the reviewer's binder-first explicit order works. The
erasure paragraph is removed and replaced by this one.

## What was done (all items of the task)

1. `grammatik/Grammatik/Syntax.lean`: `shl`/`shr` constructors now carry
   `(w : Nat) (hw1 : h1 < 2 ^ w) (hw2 : h2 < (w : Int))` before the
   existing `(h0 : 0 <= l1) (h0' : 0 <= l2)`, mirroring `bor`/`bxor`.
   Result ranges unchanged (`.int 0 (h1 * 2 ^ h2.toNat)`, `.int 0 h1`).
2. `grammatik/Grammatik/Typen.lean`: `Zahl.shl`/`Zahl.shr` take the same
   `(w) (hw1) (hw2)` premises. The `hw2` premise is USED in both bodies
   (bound into `hw2'`/`hb2` facts inside the proofs, so no premise is
   discarded); `hw1` stays `_`-named (operand bound, carried for the
   constructor match, like `bor`'s unused-in-proof widths). Result ranges
   unchanged.
3. Propagation to every use site (all former `.shl _ _ a b` patterns now
   `.shl _ _ _ _ _ a b`, terms pass the premises through):
   - `Semantik.lean`: `Expr.orte` arm + both `eval` arms (pass through to
     `Zahl.shl`/`Zahl.shr`).
   - `Satz.lean`: `orte_darf` arm.
   - `Zucker.lean`: `Expr.ins` arms (pass through); `bitfeld` takes new
     hypotheses `hw1 : 256^n - 1 < 2^(lo'+1)` and
     `hw2 : lo' < lo'+1` (they do NOT follow from the other arguments,
     so they are premises, not `sorry`s -- no `sorry` in the file) and
     passes them to `.shr`; `embeds` forwards them.
   - `Zeugnis.lean`: `CertExpr.shl`/`shr` carry `(w : Nat)`; `certRange`
     recomputes `0 <= l1 /\ 0 <= l2 /\ h1 < 2^w /\ h2 < w` (width refusal
     = `none`, like `bor`); `zeugnis_sound` shl/shr cases hand all four
     side conditions to `Expr.shl`/`Expr.shr`; probes updated
     (`.shl 32 (.lit 3) (.lit 2)` accepts; `.shl 32 ... (.lit 32)` and
     `.shr 32 ... (.lit 40)` are provably invalid -- the C UB row as a
     `decide` refusal).
   - `Extraktion.lean`, `InterferenzAllgemein.lean`: proof arms widened
     (premises flow through `rw [ha, hb]`, used via the induction
     hypotheses, not discarded).
   - `Budget.lean`: `modellKopf`/`senkKosten` arms widened (3-arg cert
     heads).
4. `grammatik/Grammatik/Schiebung.lean` (rewritten): `SpeicherBreite`,
   `rustSchiebtOk` (Rust `b.min < 0 || b.max >= a.breite` as a Lean
   predicate), `leanSchiebtOk` (read off the constructor: operand fit +
   amount bound), `shl_rust_lean_gleich` (amount legs coincide, both
   directions proved), `schiebeWeiteOk`, `shl_weite_im_c_definiert` and
   `shr_weite_im_c_definiert` (for every `Expr.shl`/`Expr.shr` term
   exhibited as such, the amount bound `h2 < w` holds -- the constructor
   premise returned; no universal over contracts/statements/`Vertrag`),
   `shl_weite_im_c_definiert_zeuge` (joint witness: `w = 32`,
   `3 < 2^32`, `2 < 32` on `3 << 2`), `schiebeSatz_rechnet`
   (`Zahl.shl ... = 12` by `rfl`). `CUTS` + five `#print axioms`.

## Verification

- `./lean-bau`: `Build completed successfully (37 jobs).`,
  `== 0 error line(s) in the COMPLETE output`.
- Axioms: `shl_weite_im_c_definiert`,
  `shr_weite_im_c_definiert` on `[propext, Classical.choice,
  Quot.sound]` (from `Expr` equality in the exhibitues premise);
  `shl_rust_lean_gleich` on `[propext]`; `..._zeuge` axiom-free;
  `schiebeSatz_rechnet` on `[propext, Quot.sound]`.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in any touched
  file (grep-verified; only prose mentions remain).
- `pruefe-praemisse.py --local` on the new theorems: INCONCLUSIVE (the
  instrument cannot address binders inside the existential exhibitues
  premise -- `hw2` is not a top-level premise name). The use of every
  premise is instead checkable by reading the proof terms
  (`obtain ... hw2 ...; exact ⟨w, hw2⟩`).
- Text guardians `pruefe-englisch.py`/`pruefe-todo.py` could not run
  (`cargo` absent, premise probe needed ssh in its default mode); new
  prose is English-only by construction.

## Names of new/changed definitions/theorems

Changed: `Expr.shl`, `Expr.shr`, `Zahl.shl`, `Zahl.shr`
(premises added, result types unchanged). New in `Schiebung.lean`:
`SpeicherBreite`, `rustSchiebtOk`, `leanSchiebtOk`,
`shl_rust_lean_gleich`, `schiebeWeiteOk`, `shl_weite_im_c_definiert`,
`shr_weite_im_c_definiert`, `shl_weite_im_c_definiert_zeuge`,
`schiebeSatz_rechnet`. Changed signatures: `Zucker.Expr.bitfeld`,
`Zucker.Expr.embeds` (two width hypotheses added);
`CertExpr.shl`/`shr` (width argument added).

## What remains open

- The Rust printer (`certemit.rs` `Shl`/`Shr`) does not print the width
  yet, so the S4/V5 printer-to-Lean leg for shifts is open (booked in
  the file's `CUTS`).
- `Zahl.shl`'s `hw1` is carried but unused in the range proof (same
  status as `bor`'s widths); a follow-up may tighten the result range
  with it.
- `bitfeld`'s `hw1` (`256^n - 1 < 2^(lo'+1)`) is owed by the caller;
  no callers exist in the tree yet.
