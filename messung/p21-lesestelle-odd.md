# LESESTELLE parser gaps -- odd half (p21)

Base: `2dc02ad`. Branch: `p21-ziel`. Owner of the ODD-numbered gaps; p22 owns the even ones.

## Adaptation (mission premise corrected, not assumed)

The mission names `grammatik/Grammatik/Syntax.lean` + `Zucker.lean` as the
gap registry. At the base commit `LESESTELLE` occurs in NEITHER file
(zero hits by `rg`; both files read in full). The actual registry is the
production-to-constructor table `messung/SYNTAX-PARSER-ENTWURF.md`, whose
"How to read" section defines LESESTELLE as surface syntax with no
constructor. Numbering below follows that file's row order, 1-based, over
its LESESTELLE rows only. Neither Lean file was touched.

## Numbering (file order over the draft's LESESTELLE rows)

| # | production | gap | owner | probe / status |
|---|---|---|---|---|
| 1 | `ident` | G-LEX | p21 | `p21-lesestelle/p21-gap01-ident.lean` |
| 2 | `letter` | G-LEX | p22 | -- |
| 3 | `digit` | G-LEX | p21 | `p21-lesestelle/p21-gap03-digit.lean` |
| 4 | `hexdigit` | G-LEX | p22 | -- |
| 5 | `int` | G-LEX | p21 | `p21-lesestelle/p21-gap05-int.lean` |
| 6 | `dec` | G-LEX | p22 | -- |
| 7 | `hex` | G-LEX | p21 | `p21-lesestelle/p21-gap07-hex.lean` |
| 8 | `bin` | G-LEX | p22 | -- |
| 9 | `float` | G-LEX | p21 | `p21-lesestelle/p21-gap09-float.lean` |
| 10 | `string` | G-LEX | p22 | -- |
| 11 | `char` | G-LEX | p21 | `p21-lesestelle/p21-gap11-char.lean` |
| 12 | `quote` | G-LEX | p22 | -- |
| 13 | `newline` | G-LEX | p21 | `p21-lesestelle/p21-gap13-newline.lean` |
| 14 | `comment` | G-LEX | p22 | -- |
| 15 | `path` | G-NAME | p21 | `p21-lesestelle/p21-gap15-path.lean` |
| 16 | `pathseg` | G-NAME | p22 | -- |
| 17 | `identlist` | G-NAME | p21 | `p21-lesestelle/p21-gap17-identlist.lean` |
| 18 | `regbind` | G-NAME | p22 | -- |
| 19 | `buildgate` | G-FILTER | p21 | `p21-lesestelle/p21-gap19-buildgate.lean` |
| 20 | `bitpos` | G-LAYOUT | p22 | -- |
| 21 | `space` | G-SPACE | p21 | `p21-lesestelle/p21-gap21-space.lean` |
| 22 | `heldpred` | G-HELD | p22 | -- |
| 23 | `inductlist` | G-SCHEME | p21 | `p21-lesestelle/p21-gap23-inductlist.lean` |
| 24 | `induct` | G-SCHEME | p22 | -- |
| 25 | `costexpr` | G-COST | p21 | `p21-lesestelle/p21-gap25-costexpr.lean` |
| 26 | `concurrentdecl` | G-CONC | p22 | -- |

Each p21 probe holds the tree-vs-token mapping rule (header comment) plus a
minimal parse witness as checked Lean examples; probes that feed a real
constructor also `#check` it. No gap was withdrawn: all thirteen odd gaps
are mappable (lexer discharge, name resolution, item-list filter,
declaration attribute, or scheme/annotation erasure).

## Deliberately untouched

- Even gaps (#2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26): p22's half.
- The `relabel` arm of `opname` (G-RELABEL): a core row with a gap arm, not
  a LESESTELLE row, hence unnumbered and outside the odd/even split.
- `SYNTAX.md`, the draft, `Syntax.lean`, `Zucker.lean`: no edits.

## Open finding (flagged, not fixed)

The draft and `SYNTAX.md` section 16.2 quote a census of 25 LESESTELLE rows
(124 core + 12 SUGAR + 25 = 161). Counting `| LESESTELLE` rows in the draft
gives 26 (18 lexis/name rows + buildgate, bitpos, space, heldpred,
inductlist, induct, costexpr, concurrentdecl). The census is off by one
somewhere; the numbers were left as they stand because guardians quote them.

## Verification

Each probe elaborated with the toolchain Lean 4.33.1 (`leanprover/lean4:v4.33.1`,
same as `grammatik/lean-toolchain`), LEAN_PATH pointed read-only at the main
checkout's prebuilt oleans
(`programmlogik/.lake/build/lib/lean:grammatik/.lake/build/lib/lean`; this
worktree carries no `.lake` build and `lake` builds are out of scope while
the server is down). All 13 files exit 0, sequentially with staggered sleeps
under the `free -g` gate. Two toolchain notes are booked inside the probes:
`String.trim` changed type (gap17 carries a local trim) and
`String.splitOn` does not reduce definitionally here (gap17 splits
explicitly over `List Char`).
