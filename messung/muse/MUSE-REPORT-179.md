# MUSE-REPORT-179 — T3: the round-trip induction finished level by level

Lane 179, branch `muse/179`. Task: in a NEW file
`Parser/Rundlauf3.lean` (importing `Rundlauf2`), widen the
predicate level by level in the order of MUSE-REPORT-172 "Open"
(comparisons, bit operators, remaining add/mul spellings, calls
with argument lists, `sizeof`/`lenof`/`aligned`), one green
commit per level, and at the end prove `parse_druck` for lane
161's full `gut` if all levels are in, else for the widest
predicate with the exact remaining blocker. Witnesses
discipline (corpus expressions per level). No codes, gifts or
examples reserved (none used).

## Status: all five levels green; round trip proved for `gutEmb`

`./lean-bau` last lines:

```
✔ [200/201] Built Grammatik (201ms)
Build completed successfully (201 jobs).
```

(`./lean-probe` on `Rundlauf3.lean`: exit 0, 0 errors; only
unused-simp-arg linter warnings — same class as lanes 161/172.)
No Rust touched. `Ausdruck.lean`, `Rundlauf.lean`,
`Rundlauf2.lean` NOT edited. `Grammatik.lean` gains one import
line. No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`
anywhere (grepped); every theorem premise is used (no
unused-variable linter warnings).

## What was built (all in `grammatik/Grammatik/Parser/Rundlauf3.lean`, 2422 lines, 101 defs/theorems)

Architecture (committed first as the scaffold): instead of
re-running lane 172's joint size induction per level, the file
works with predicate-free legs — every B-step in `Rundlauf2`
uses its invariant only at strict subterms, and every tower
takes its B-leg as a hypothesis, so:

- `Legs e`: the eight fuel-generalised round-trip legs for ONE
  fixed tree (the `RKern` leg shapes with size bound and
  predicate dropped).
- `legsKern`: every `gutKern` tree has legs (repackaged
  `kernRB` at `groesse e`).
- one generic B-step per operator group (operand legs plus
  op-table facts as hypotheses, no predicate anywhere), one
  generic spelling-blind tower `bin_turm3` (B-leg to eight
  legs; `kern_bin_turm`'s two `gutKern` premises were never
  used by its own proof).

Each level defines its predicate as the previous predicate
plus ONE new layer over the previous predicate's trees, and
proves legs from the previous level's legs. Per level:

- CMP: `cmp_is` (six spellings), `cmpbar_facts` bundle,
  `opVgl_cmp_hit`, `tower_up_cmpbar` (three loops below the
  single-shot level), generic `cmpB_step` (same `+10` fuel),
  `cmpLegs`, `gutCmp`, `legsCmp`, `parse_druck_cmp`.
- BIT: `bit_is`, `bitbar_facts`, `opBit_bit_hit`,
  `tower_up_bitbar`, generic flat-loop `bitB_step` (the `+`
  shape one level up), `bitLegs`, `gutBit`, `legsBit`,
  `parse_druck_bit`.
- ADD/MUL-REST: `add_is`/`mul_is`, `addbar_facts`,
  `opAdd_add_hit`, `mulbar_facts`, `opMul_mul_hit`,
  generic `addB_step` (mirrors `kernB_step`) and `mulB_step`
  (mirrors `kernB_step_star` including its numeral-fold
  unfold), `addLegs`/`mulLegs` (cover all five/four
  spellings — overlap with older predicates is harmless),
  `addNeu`/`mulNeu`, `gutAM`, `legsAM`, `parse_druck_am`.
- CALLS: bridges `gut_of_gutCmp`/`gut_of_gutBit`/`gut_of_gutAM`
  to lane 161's `gut`, so `keinDP_tree` and `toksKopf` are
  reused directly (no analogues — the 172 estimate assumed an
  `RKern` adaptation; instantiating at the tree's own size
  needs no bound). `arg_legs`/`args_legs` mirror
  `arg_einzeln`/`args_rund`, `prim_ruf_legs` mirrors
  `prim_ruf`, `rufLegs` climbs `tower_up` (the `ident` head
  fires no prefix arm). `gutListeAM` plus head/tail/bridge/
  legs-list helpers, `rufNeu`, `gutRuf`, `legsRuf`,
  `parse_druck_ruf`.
- BUILTINS: `suffGutKern_idx`, Legs-version suffix runner
  `suff_legs` (no size bound threads through — payload legs
  come straight from `legsKern`), `ort_legs_kern` (mirror of
  `ort_platz_all` over `zerlege_kern`), `parseEingebaut_ein`/
  `_zwei` as definitional rewrites, `prim_emb1_legs` (both
  spellings, gate by `eingebaut_ein_ok`),
  `prim_aligned_legs` (two Or-legs), generic `embTower`,
  `sizeofLegs`/`lenofLegs`/`alignedLegs`, bridge
  `gut_of_gutRuf`, layers `sizeofNeu`/`lenofNeu`/
  `alignedNeu`, `gutEmb`, `legsEmb`, `gut_of_gutEmb` (via
  lane 161's `gut_sizeof_one`/`gut_lenof_one`/
  `gut_aligned_two`), `parse_druck_emb`.

Widest green predicate (`gutEmb` = level 4 `gutRuf` plus one
builtin layer each):

```
parse_druck_emb : ∀ (e : SExpr), gutEmb e = true →
  parseOr (brennstoff e) (druckToks e ++ [.ende]) =
    .ok (e, [.ende])
```

Eleven witnesses, each as a round-trip instance plus a
kernel-computed `match` check: `==` (field vs literal, after
`01-tabelle`), `<` (counter bound, after `04-schleifen`),
`&` mask and `<<` shift (after `45-gemischte-
registerklasse`), binary `-` and `/` (after `04-schleifen`),
one- and two-argument calls (after `107-summe-zwei-rufe`),
`sizeof`/`lenof`-over-a-field (`02-geraet`/`04-schleifen`)
and an `aligned` pair.

## Open: full `gut` NOT proved — the exact remaining blocker

The five ordered levels are all in, but full `gut` needs
three things outside them (all named in 172's report as
"not started", none of them a level):

1. **Places over full `gutPlatz`** (the load-bearing gap).
   Every place layer here is `gutKernPlatz`: variable-based,
   kernel payloads. Full `gut` admits `feld`/`index`/`pfeil`
   over arbitrary `gutPlatz` bases with `gut` payloads. The
   runner generalisation is cheap (`suff_legs` already takes
   payload legs straight from the predicate — feed it
   level-5 legs instead of `legsKern`), but the PREDICATE
   restructuring is not: a wider place predicate must be
   defined mutually with `gutEmb` (index base vs payload),
   and `gutEmb`, `gutListeAM`, `argsRuf2` plus every
   downstream layer already bake in the non-recursive shape.
   Cost: touching every level's predicate, re-proving every
   legs theorem's place arms. This is the one gap that takes
   a day, not an hour.
2. **Four single-constructor primaries**: `alt` (`old` —
   `prim_alt` exists in lane 161; over kernel places it is a
   `ort_legs_kern` mirror, ~40 lines), `ergebnis`
   (`prim_ergebnis` exists; atom tower, ~30 lines), `grund`
   (`G::F` — `prim_grund` exists with its four gates;
   ~50 lines), `fnwert` (`&`-paths need segment acts at the
   unary level — the only one of the four with new parser
   machinery, ~80 lines).
3. **Nesting depth**: each layer covers ONE new-constructor
   layer over the previous predicate — a call's arguments
   are level-3 (`gutAM`) trees, so calls cannot yet nest in
   call arguments, and builtins cannot nest in builtins.
   Arbitrary nesting needs the joint size induction over a
   recursive predicate (lane 172's architecture, ~500 lines
   to replay the four old B-steps over abstract legs). The
   `Legs` conveniences built here (`bin_turm3`,
   `tower_up_*bar`, `embTower`, `args_legs`) transfer
   verbatim — only the four old B-steps and the place arms
   need replaying.

## Findings about the task (rule 12 notice)

1. Nested list patterns in predicate defs (`.eingebaut w
   [x]`) generate equation lemmas `simp` never fires on
   (measured: 74 "made no progress" in one probe). Payload
   lists live in their own one-level defs (`argsPlatz1`,
   `argsRuf2`) — flat patterns reduce like `gutKern`.
2. `have rfl : f = w` substitutes nothing; only `obtain`'s
   `rfl` pattern or `subst heq` rewrite the goal (measured:
   three "type mismatch ... expected `Legs (.eingebaut f
   …)`" plus three failed `rw`s from the same cause).
3. The `||` chain associates left: in a four-way predicate
   the THIRD disjunct binds second, not third. Two whole
   branch bodies were written swapped and every `simp` in
   them failed — each failure looked local, the cause was
   thirty lines above in the `obtain` order. (Name
   hypotheses after their predicate, not their position.)
4. `tower_up`'s Unary-leg premise takes NO `ruhig`
   premises; a `Legs`-shaped Unary leg must be wrapped
   (`fun G hG => hU rest' G hrs hrg hG`) at each of the six
   call sites.
5. `args_rund`'s mirror needs lane 161's exact side facts:
   `have hxp := groesse_pos x` before the tail fuel
   (omega fails without it) and `nil_append` for the
   leading `[] ++` the `parseKopf` rewrite leaves behind.
6. `parseEingebaut`'s `n == 1`/`n == 2` tests reduce
   definitionally — the one/pair splits are plain `rfl`
   rewrites, which is why the "resisted" level cost ~350
   lines, not the estimated 200 plus analogues.

Commits on `muse/179` (each green at commit time): scaffold
+ comparison level, bit level, add/mul-rest level, calls
level, builtins level, this report; nothing outside
`grammatik/` and `messung/muse/` touched; no network/`cargo`/
`ssh` used.
