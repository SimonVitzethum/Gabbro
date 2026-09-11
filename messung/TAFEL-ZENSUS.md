# Tafel census — all open ruling-table slots (Phase 0, docs only)

*Base: `2dc02ad`. Measured 2026-09-11, local lane (server unreachable),
worktree `.claude/worktrees/p01`, branch `p01-ziel`. No code changed.*

## Scope

The ruling table is `tafel : List EntscheidZiel` in
`grammatik/Grammatik/Erhaltung.lean`: 19 named `CForm` shapes plus 30 census
slots (`OffeneForm`), each carrying a `RulingStatus`
(`offen` | `aufListe preis` | `ausErzeuger ersatz`). A slot is **open** iff
its table row carries `.offen`. `dokumente/SYNTAX.md` §21 (lines 1711–1838)
holds the prose contract; it names no per-slot rows — every `file:line`
below therefore points into `Erhaltung.lean`.

## Recompute (every number names its command)

Run from the tree root:

```bash
# Open table rows (anchored; the count that matters):
rg -n '^\s+\.luecke \.\w+ \.offen,$' grammatik/Grammatik/Erhaltung.lean
rg -c '^\s+\.luecke \.\w+ \.offen,$' grammatik/Grammatik/Erhaltung.lean
# → 8

# All table slot rows (open + ruled):
rg -c '^\s+\.luecke' grammatik/Grammatik/Erhaltung.lean
# → 30

# Ruled slot rows (21 inline statuses + line 299 `bedingt`, ruled via `bedingtEntscheid`):
rg -n '^\s+\.luecke \.bedingt' grammatik/Grammatik/Erhaltung.lean
# → 299:   .luecke .bedingt bedingtEntscheid,

# Prose mentions of `offen` inside SYNTAX.md §21 (no per-slot rows there):
rg -n 'offen' dokumente/SYNTAX.md | awk -F: '$1>=1711 && $1<=1838'
# → 1780, 1790, 1797 (prose only)
```

Result: **8 of 30 slots open, 22 ruled.** (A naive unanchored grep for
`\.offen` reports 9 hits because line 666 — the `have hm` step of
`tafel_nicht_geschlossen` — also matches. The anchored form above is the
census; the naive form is the trap.)

## Class key (mission labels, defined here)

The six labels are the mission's working set, not tree terms; each row
below carries a one-line reason so the assignment stays checkable:

| label | meaning for this census |
|---|---|
| CForm | slot needs a named-shape admission onto the §18 list (`aufListe` with priced semantics) |
| H | slot touches hardware/axiom-adjacent practice (priced-option pattern of `beschraenkt`/`fluechtig`) |
| V | slot touches vocabulary/lexis the grammar never names (preprocessor, spellings) |
| M | slot needs a model-side discharge (Lean `Ziel`/alias/cost obligation), not just a list row |
| RACE | slot gated on the race/interleaving discipline |
| W | slot closable purely by generator removal plus a witness pair (`ausErzeuger` path, no new semantics) |

## Census table

Census class and site counts quote the `OffeneForm` doc lines
(`Erhaltung.lean` lines 211–242).

| slot | file:line | class | blocked-by | suggested owner wave |
|---|---|---|---|---|
| `zeigerArithmetik` | `grammatik/Grammatik/Erhaltung.lean:293` | M — contradicts §2 row 2 as written; discharge is the alias obligation (`satz_alias`, §21.2), not a list row | alias leg (`AliasObligation`, `ptrArithCensus = 491`) + rewrite of the `basisPlus`/`bytesPlus` emission sites; the debt proof `tafel_nicht_geschlossen` (lines 663–668) hangs on this row | Wave 3 (last — keep the debt proof failing until everything else is ruled, so the guard keeps guarding) |
| `cInclude` | `grammatik/Grammatik/Erhaltung.lean:295` | V — preprocessor lexis outside the grammar (C1, 408 sites) | preprocessor-scope ruling (everything beyond `#if`); generator removal or priced admission | Wave 1 (mechanical) |
| `cTypedef` | `grammatik/Grammatik/Erhaltung.lean:296` | CForm — declaration-shape admission against the typedef-free list (C1, 240 sites) | typedef-free list revision; `aufListe` price or generator removal | Wave 1 (mechanical) |
| `cDefine` | `grammatik/Grammatik/Erhaltung.lean:297` | V — constant spelling lexis; "enum-free constants" plainly means it (C1, 210 sites) | constant-spelling ruling; generator removal or priced admission | Wave 1 (mechanical) |
| `cEnum` | `grammatik/Grammatik/Erhaltung.lean:298` | CForm — type-declaration admission against the enum-free list (C1, 28 sites) | enum-free list revision; `aufListe` price or generator removal | Wave 1 (mechanical) |
| `voidTyp` | `grammatik/Grammatik/Erhaltung.lean:300` | CForm — missing type row (the type row never names it; C2, 930 sites, the largest open count) | type-row admission with priced semantics + witness pair (§21.5) | Wave 2 (semantic admission) |
| `cAttribut` | `grammatik/Grammatik/Erhaltung.lean:301` | H — attributes ride on carrier/placement practice beside `beschraenkt`/`fluechtig` (C2, 766 sites) | priced-option ruling on the `beschraenkt`/`fluechtig` pattern + witness pair | Wave 2 (semantic admission) |
| `cSizeof` | `grammatik/Grammatik/Erhaltung.lean:309` | CForm — operator-shape admission (C2, 27 sites, the smallest open count) | operator-row ruling; `aufListe` price or generator removal | Wave 1 (mechanical) |

Findings beside the table:

- **RACE owns zero open rows.** No open slot is concurrency-gated; that is itself a result (the race discipline is not on the critical path of the table).
- **W owns zero rows directly.** Every open slot still needs a semantic decision first; the `ausErzeuger` path becomes available only after the ruling (as `bedingt` showed: `bedingtEntscheid`, line 249–250, is the single filled template).
- **SYNTAX.md §21 contributes prose, not rows.** Its three `offen` mentions (1780: status-field definition; 1790: "stand `offen`, with two exceptions"; 1797: "`satz_tafel` … FALSE today") name no slot and carry no line-anchored status. The machine-readable census lives only in `Erhaltung.lean`.

## Risks (stale numbers the census exposes)

1. **Four prose counts disagree with the table and all err in the same
   direction.** `Erhaltung.lean:71` ("the 29 open slots"), `:271` ("the 30
   census slots open — except `bedingt`"), `:352` ("29 slots still `offen`"),
   and `SYNTAX.md:1796–1797` ("29 slots still `offen`") predate the lane-121
   rulings (`zeigerIndex`, `abbruchStmt`, `logUndOder`, `fortStmt`, and the
   rest — 22 of 30 now ruled). Measured open count is **8**, not 29. The
   theorems still hold (`tafel_nicht_geschlossen` needs only one open row),
   but every English sentence quoting 29/30 is stale.
2. **The naive reproducer overcounts by one.** Unanchored `rg '\.offen'`
   matches line 666 (proof step, not a table row) for 9 hits. Only the
   anchored command in the Recompute section is the census.
3. **`bedingt` is ruled but invisible to the inline-status grep.** Line 299
   carries `bedingtEntscheid` instead of an inline constructor, so the
   ruled-row count needs two commands (21 inline + 1 named). A future ruling
   in the same style will silently shift that split again.
4. **Class labels are mission-local.** CForm/H/V/M/RACE/W appear nowhere in
   the tree; the key above is the only definition. If the labels get reused
   in later phases, pin this file as their source.
