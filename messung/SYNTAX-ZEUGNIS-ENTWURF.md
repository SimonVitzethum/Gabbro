# The derivation certificate as a SYNTAX.md section — draft

Status: DRAFT ONLY, no implementation, no edits to SYNTAX.md itself.
Worktree lane-92, base 536e118. This file is the SYNTAX.md section draft;
dokumente/SYNTAX.md is untouched.

Goal: give the certificate side of the S4/V5 witness pair
(grammatik/Grammatik/Zeugnis.lean) a prose section in SYNTAX.md, so that a
reader who never opens the Lean file still learns what a certificate is,
what each form carries, what the table recomputes, why a forgery fails by
construction rather than by diagnostic, and what is still booked and who
owns it.

Source sentences, all read on this tree:

- Zeugnis.lean header (lines 1-73): what stands here, trust base, cuts.
- certRange (lines 205-284): the per-form range table with side conditions.
- GueltigAbleitung (lines 289-291): validity as recomputed equality.
- zeugnis_sound (lines 299-597) and block_sound (lines 865-893): soundness.
- CUT-1/CUT-2 decide probes (lines 710-752), CUT-4 probes (lines 754-797),
  CUT-5 probes (lines 895-935).
- CertBlock and certBlockGueltig (lines 811-834).

## 1. What a certificate is

A certificate is a derivation term as plain data. The CertExpr inductive
(line 168) mirrors the Expr constructors of the same shape, but the
hypothesis fields are absent: the claimed result range travels beside the
term as the argument pair of GueltigAbleitung, and every side condition is
recomputed by certRange on the Lean side, never trusted from the print.
The three read shapes carry declaration data only — a de Bruijn index, a
global name, a table with field and index expression — never proofs.

Validity is one equation: the printed claim pair equals exactly what the
table recomputes (line 289). Wherever the world is concrete the equation
is decidable, so acceptance and rejection of a print both close by decide.

Soundness is the direction this construction owns: a valid certificate
implies the judgment, i.e. elaborates to a real Expr term, an accepted
derivation (zeugnis_sound, line 299). The induction is over the
certificate; each case hands the recomputed side conditions to the
corresponding Expr constructor. The statement is an existence, not the
term itself: the judgment is the proposition that the derivation exists,
the witness-pair shape of S4/V5.

The trust base is explicit and stays where PLAN-UMSETZUNG.md section 1.3
books it: the Rust printer (gabbro lean / gabbro-ableitung) is trust base
here. The file proves valid-print-implies-judgment, not
printer-prints-what-checker-derived. A printer that prints a different
derivation than the one it checked is outside this construction, exactly
as section 1.3 books it: the print, not the printer, is what Lean checks.

## 2. CertExpr validity table

Each row names the form, the range the table recomputes, and the side
condition that must hold for the table to yield a range at all. A failed
side condition yields no range (none), not an error message. The bounds
are written exactly as in the Expr constructors of Syntax.lean section 3,
so whatever certRange computes for a valid certificate is definitionally
the index of the Expr term zeugnis_sound builds.

| form | recomputed range | side condition, recomputed |
|---|---|---|
| lit n | (n, n) | none |
| add a b | (l1 + l2, h1 + h2) | both subterms yield ranges |
| sub a b | (l1 - h2, h1 - l2) | both subterms yield ranges |
| neg a | (-h1, -l1) | subterm yields a range |
| mul a b | min and max over the four corner products | both subterms yield ranges |
| div a b | (0, h1) | dividend nonneg and divisor above zero, i.e. 0 ≤ l1 and 1 ≤ l2 (M102) |
| rem a b | (0, h2 - 1) | same pair as div (M102); the bound comes from the divisor |
| sdiv a b | (-betragMax, betragMax) over the dividend | divisor excludes zero, i.e. 1 ≤ l2 or h2 ≤ -1 (second sentence of SG-3) |
| srem a b | (-(betragMax - 1), betragMax - 1) over the divisor | same zero-exclusion as sdiv |
| band a b | (0, h1) | both operands nonneg, i.e. 0 ≤ l1 and 0 ≤ l2 (M137) |
| bor w a b | (0, 2 ^ w - 1) | both operands nonneg and both upper bounds below 2 ^ w (M137 plus width) |
| bxor w a b | (0, 2 ^ w - 1) | same width rule as bor |
| shl a b | (0, h1 * 2 ^ h2nat) | both operands nonneg |
| shr a b | (0, h1) | both operands nonneg; a right shift never widens (M137) |
| wide lo hi a | (lo, hi) | containment, i.e. lo ≤ l1 and h1 ≤ hi |

Notes on the table:

- CUT-1 (signed division and remainder) is the sdiv/srem pair: the
  zero-exclusion is a disjunction over the divisor range, and the srem
  bound is drawn from the divisor while the sdiv bound is drawn from the
  dividend. Both rows, validity side conditions, soundness cases and
  probes are covered in Zeugnis.lean.
- CUT-2 (bitwise and shifts with width proofs) is the band/bor/bxor/shl/
  shr group: nonnegativity throughout, the width bound h < 2 ^ w for bor
  and bxor, the shift-cost bound for shl, the never-widens bound for shr.
  Same coverage shape as CUT-1.
- M104 is the shape rule behind the arithmetic rows; M102 is the
  nonneg-dividend, positive-divisor pair for div and rem; the second
  sentence of SG-3 is the divisor-excludes-zero disjunction for sdiv and
  srem; M137 is the nonneg rule with the width bound for the bitwise
  group.

## 3. Reads: variables and carrier accesses

CUT-4 is covered for the int fragment. The closed fragment never looks at
the variable context or the resource context; the read shapes do, and only
through total functions, so decide evaluates them wherever the world is
concrete.

| form | recomputed range | side condition, recomputed |
|---|---|---|
| var k | ctxTyp of index k in context Gamma | the lookup hits an int-typed entry; the Var witness is rebuilt here, never trusted from the print |
| glob g | declared type range of g | carrier is int-typed (intVonTyp says some) and the guard gdarf holds under the current resources |
| slot t f i | field type range of f in table t | index recomputes exactly the generated index type 0 .. count - 1, carrier is int-typed, and the guard darf holds |

Three points the table enforces and the prose must keep:

- A bare literal is not an index until wide says so: the slot arm
  demands the index range be exactly the pair (0, count - 1), so an
  unwidened literal has no range and the read fails closed.
- Reads of non-int carriers (a bool-typed global, a pointer-typed slot)
  land on none in intVonTyp: booked, not faked.
- The guards darf and gdarf quantify over a finite needs list with
  decidable membership, so the table recomputes them with a conditional
  instead of trusting them from the print.

## 4. CertBlock shapes: straight-line statements over int bindings

CertBlock (line 811) is the printed certificate for a Block, with
certBlockGueltig (line 825) as its validity predicate: the structural
checks the table recomputes. Decidable wherever the world is concrete, so
block acceptance and rejection both close by decide. Block soundness
(block_sound, line 865) says a valid block certificate implies the
judgment: there exists an accepted Block.

| shape | what the certificate carries | what validity recomputes |
|---|---|---|
| nil | nothing | True: the checks live in the statements, not in the sequencing |
| bind e lo hi rest | expression, claimed range, tail | certRange of e equals (lo, hi); tail checked in the extended context (int lo hi cons Gamma) |
| call f hp rest | callee name, RufPasst proof, tail | params empty and gruende zero, recomputed; tail checked after the callee transition |
| ret | nothing | result shape empty (erg none) and the linear balance (resources permute to the owed end) |
| retWert e lo hi | expression, claimed range | result shape matches (erg some int lo hi), certRange of e equals (lo, hi), and the linear balance |

The CUT-5 remainder travels inside call and says so out loud (see
section 6): the nullary shape is recomputed, but RufPasst itself travels
as proof.

## 5. Forgery fails by construction, in prose

Every example below is a decide probe in Zeugnis.lean, restated without
code: each names a print and the verdict Lean returns. A forged or
mismatched print is not rejected with a message; it is provably invalid,
and no acceptance proof can be built from it.

- A mismatched sum: one plus two printed as the pair (0, 0) is provably
  not valid, while the same term printed as (3, 3) is accepted.
- A forged quotient: five divided by zero printed with any claim has no
  range, because the divisor range admits zero and the M102 condition
  fails; five divided by two printed as (0, 5) is accepted.
- A forged widening: twenty claimed inside 0 .. 10 has no certificate,
  while five widened to 0 .. 10 is accepted.
- Signed division and remainder: seven sdiv two printed as (-7, 7) is
  accepted; the same claim over a zero divisor is provably invalid.
  Seven srem two printed as (-1, 1) is accepted, with the bound drawn
  from the divisor; over a zero divisor the same claim fails.
- Bitwise: six band three printed as (0, 6) is accepted; a negative
  operand under band has no range. Six bor three in width three printed
  as (0, 7) is accepted; in width two, which does not hold six, the width
  side condition fails. The bxor pair reads the same. Three shl two
  printed as (0, 12) is accepted; a negative value shifted has no range.
  Twelve shr two printed as (0, 12) is accepted; a negative value shifted
  right has no range.
- Variables: index zero in a one-entry context of 3 .. 3 printed as
  (3, 3) is accepted; claimed as (0, 0) it is provably invalid. Index
  five in a one-entry context dangles and has no range. Index zero over a
  bool entry mistyped as an int range has no range. A read lifts through
  arithmetic: x plus one with x in 3 .. 3 printed as (4, 4) is accepted.
- Guards: the test global printed as (0, 7) under the held lock is
  accepted; with empty hands the guard fails and the table yields no
  range. The place read with its index widened to the generated index
  type 0 .. 10 under the held guard is accepted as the field range; the
  bare unwidened literal as index has no range; the widened index with
  empty hands has no range.
- Blocks: a binding of one claimed as (1, 1) with an empty tail is
  valid. A bare return with empty hands against a contract that holds
  nothing is valid, while a return holding a lock with nowhere to return
  it is provably no certificate — the linear failure, loud. Let x be one
  and return x against the matching value contract is valid; the return
  claimed as (2, 2), or the binding claimed as (9, 9), fails. The nullary
  call followed by return is accepted; a call with a parameter goes
  through RufPasst but fails the recomputed params-empty check, and the
  certificate is honestly rejected.
- End to end: a valid expression print yields an accepted derivation
  through zeugnis_sound, a valid variable print yields its derivation,
  and a valid block print yields an accepted block through block_sound.

## 6. What is still booked, with owners

- CUT-3 remainder: floats, options, sums, grounds, quantifiers, reaches.
  Still booked. The fragment is int-typed throughout: every certificate
  elaborates to an Expr of int type (reads) or a Block over int bindings
  (statements). Non-int types — bool, pointers, functions, options,
  sums — stay booked here. Owner: grammar lane for the shapes,
  semantics lane for the float leg (a float operation range is the
  machine's rounding, i.e. a hardware assumption by the letter of the
  task; SYNTAX.md section 16.2 row 5 already carries it as hardware
  ieee).
- CUT-4 remainder: durch, ptrOf, fnref, altGlob, altSlot. Still booked.
  Pointer and function types carry no range, so the range table has
  nothing to recompute for durch, ptrOf and fnref; altGlob and altSlot
  are post-entry values, not reads of the live world. Owner: grammar
  lane (constructor coverage in Syntax.lean and the certificate arms
  that follow it).
- CUT-5 remainder: a call's RufPasst travels as proof in the
  certificate. It quantifies over the arbitrary carrier types, so no
  range table can recompute it the way certRange recomputes darf;
  carrying it is the honest shrink. The day Tab and Glob enumerate, the
  arm can check it instead of carrying it. Owner: proof-architecture
  lane (enumeration of the declaration families and the checking arm).

## 7. Placement proposal

The section belongs to section 21, the producer contract: the certificate
is what the emitter must uphold per run in checkable form, and the
derivation certificate is its Lean-side half (section 21.5 holds the
witness pairs, the executable half). Proposed placement: a new subsection
after 21.5 (witness pairs) and before the current 21.6 (what this section
does not move), numbered 21.6, with the current 21.6 moving to 21.7
unchanged. The current 21.6 already books the certificate as specified
but the recomputer as a later program; the new subsection fills in what
the specified certificate is, per form, without moving that booking.

Proposed section structure inside the new subsection:

- What a certificate is: plain data, recomputed table, validity as one
  equation, soundness direction, trust base (printer stays trust base).
- The validity table: one row per CertExpr form with recomputed range
  and side condition (sections 2 and 3 above, with the M102 / SG-3 /
  M137 provenances).
- The block shapes: the five CertBlock shapes with what validity
  recomputes (section 4 above).
- Why forgery fails by construction: the decide probes restated in
  prose (section 5 above), ending with the end-to-end yields.
- What is still booked: CUT-3, CUT-4 remainder, CUT-5 remainder, each
  with its owner (section 6 above).

Deliberate omissions in the draft, decided loudly:

- No grammar productions: the certificate is printed data about
  derivations, not source syntax; it adds no EBNF rule and no vocabulary
  word, so the guardians that count rules and words see no change.
- No Lean code in the section: constructor names and theorem names are
  cited as names with file and line pointers, never pasted; the section
  stays readable without the file open.
- No numbers in bold inside tables: plain figures only, so the counting
  guardians read the same values the prose states.
- No closed claims: every remainder names its owner and the condition
  that discharges it (enumeration for CUT-5, constructor coverage for
  CUT-4, the hardware booking for floats).
