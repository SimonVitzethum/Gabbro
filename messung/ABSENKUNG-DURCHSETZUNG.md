# Lowering enforcement — per-primitive statement budget in `absenkung.rs`

Date: `2026-09-11`. Base: `6f26e76`. Lane: `lane-145`.

The lowering contract in `grammatik/Grammatik/Ziel.lean` assumes every
Gabbro primitive lowers to a bounded list of C forms (`proPrimitiv <=
18`, witnessed by the measured maximum `17`). Until now nothing in the
checker held the emitter to that number: a primitive that lowered to
`19` statements would emit, compile, and pass, and no line would say
the contract no longer holds. This file books the enforcement — the
mechanism, the hook that applies it, and what is still missing.

Scope kept: two files created, none edited. `crates/gabbro-check/src/`
gains `absenkung.rs`; this file is the other. In particular `lib.rs`
carries no new `mod` line (the pass list and the module register are
owned centrally) and `emit.rs` carries no new call (the hook below is
specified, not applied).

## 1. The bound and where it comes from

```
proPrimitiv : Nat
begrenzt : proPrimitiv <= 18
def absenkung : Absenkung := ⟨17, by decide⟩
```

`17` is the statically counted maximum per Gabbro primitive, at
`Schleife`, subform `traverse over descendants of` (`nachfahren`,
`emit.rs:8523-8560`); `18` is that maximum plus one headroom. Both
figures are from `messung/ABSENKUNG-MESSUNG.md` section 4, recounted in
`messung/ABSENKUNG-SCHRANKEN-ENTSCHEID.md` section 2 (`3 + 3 + 1 + 2 +
4 + 2 + 2 = 17`). The module repeats them as constants, not as
parameters:

```
STATEMENTS_PER_PRIMITIVE = 18
MEASURED_MAXIMUM = 17
```

A bound passed as an argument is a bound the caller can move; a bound
written as a constant beside the Lean sentence is a bound a reader can
hold against it. The headroom direction is fixed the same way: the
runtime lexer pass (`messung/ABSENKUNG-ZAEHLUNG.md` section 2) can only
confirm `17` or raise it, never lower it below `17`. A rise to `18`
fits the bound; a rise past `18` moves the bound again — in `Ziel.lean`
first, here second.

## 2. The enforcement mechanism

The module (`crates/gabbro-check/src/absenkung.rs`, `std` only, no
crate imports) has three public items:

```
count_c_statements(c: &str) -> usize
check_primitive(primitive: &str, emitted: &str) -> Result<usize, OverBudget>
PRIMITIVES: [&str; 17]
```

`count_c_statements` is the measurement lexer, moved into the checker:
one `;` in emitted C text is one statement, with three exclusions from
`messung/ABSENKUNG-MESSUNG.md` section 1 (`for (...; ...; ...)`
header separators, `//` and `/* */` comment text, refusal strings —
which never reach the output buffer) plus a fourth the static
measurement never needed: `;` inside string and character literals
(`"a;b"`, `';'`). The static pass read format strings out of the
emitter source, where no literal carries a `;`; the enforcement reads
emitted text, where one someday could. Excluding them refuses LESS,
and the direction is booked in the module head rather than hidden in
the lexer.

`check_primitive` holds one primitive against the bound: it counts the
statements in the fragment the emitter produced for exactly that
primitive, returns the count when it fits, and refuses when it does
not. The refusal (`OverBudget`) names the primitive, the counted
statements, the bound, and the first `512` characters of the emitted
fragment — the named C code beside the refusal, not the whole file
behind it. Twelve unit tests inside the module cover the boundary
(`17` held, `18` held, `19` refused), each lexer exclusion, the
17-row registry, and the no-early-stop property: statements past the
bound are still counted, so the refusal states the true count, not
the bound plus one.

`PRIMITIVES` is the seventeen `StmtArt` variant names in enum order —
the row registry the hook maps each lowering arm to. One row per
variant, no more: a primitive the emitter lowers without an arm has
no row, and the hook has nowhere to hang its name.

## 3. The hook specification — the ONE call site

The enforcement is applied in exactly one place, and it is not in
this lane. Call site: `emit.rs`, `fn anweisung` (`emit.rs:6654-7755`):

```
fn anweisung(
    s: &Stmt,
    aus: &mut String,
    u: &Namen,
    absagen: &mut Absagen,
    tiefe: usize,
    austritt: &Austritt,
)
```

`Stmt` carries both facts the hook needs (`pub struct Stmt { pub art:
StmtArt, pub span: Span }`, `crates/gabbro-syntax/src/ast.rs:1158`):
the variant for the row name, the span for the refusal. The buffer
`aus` is shared across statements, so the hook slices it: one line at
the top of `anweisung` records the mark, one line at the bottom checks
the slice. Signature of the central wrapper, beside `anweisung` in
`emit.rs`:

```
fn absenkung_anwenden(s: &Stmt, fragment: &str, absagen: &mut Absagen)
```

Concretely, central adds:

```
let marke = aus.len();                       // top of `anweisung`
absenkung_anwenden(s, &aus[marke..], absagen); // bottom of `anweisung`

fn absenkung_anwenden(s: &Stmt, fragment: &str, absagen: &mut Absagen) {
    let name = match &s.art {
        StmtArt::Let(_) => "Let",
        // ... one arm per variant, names from `absenkung::PRIMITIVES`
    };
    if let Err(zu_viel) = crate::absenkung::check_primitive(name, fragment) {
        weigere(absagen, s.span, &zu_viel.to_string());
    }
}
```

The refusal reuses the existing emitter refusal `weigere`
(`emit.rs:2542`), which issues `C001 "no lowering: {was}"`. No new
refusal code, no new pass, no new register: an over-budget primitive
reads like every other named refusal of the emitter, and the
`OverBudget` display text is written to fit that slot.

Why the slice and not the whole buffer: nested body statements are
booked on the body, not on the row (`messung/ABSENKUNG-MESSUNG.md`
section 1). `&aus[marke..]` holds exactly the scaffold the primitive
itself emitted for this statement — the same direct-scaffold reading
the `17` was counted under. Counting the whole buffer would charge
every primitive for its sisters.

## 4. What was expressly not done here

- No registration: `lib.rs` is untouched, so the module compiles
  standalone and `cargo check -p gabbro-check` reads the crate
  unchanged. The module is written to compile unchanged the day
  central adds the single `pub mod absenkung;` line — `std` only, no
  crate names anywhere.
- No application: `emit.rs` is untouched. The hook above is a
  specification with line numbers and a signature, not a call.
- No new refusal code and no new pass number: the refusal is `C001`
  through `weigere`, and the module owns no sentences.
- No bound change: `STATEMENTS_PER_PRIMITIVE` repeats the `18` from
  `Ziel.lean`; it does not re-derive it.
- The runtime half of `messung/ABSENKUNG-ZAEHLUNG.md` section 2
  (minimal units, real `emit` outputs, one lexer) is still missing.
  When it lands and confirms `17`, the hook turns from specified to
  applied with the numbers already in place; when it raises the
  maximum past `18`, the bound moves first in `Ziel.lean`, then here.

Evidence beside the mechanism: `rustc --test` over the single new
file (twelve tests, all green), `cargo check -p gabbro-check` over
the untouched crate (green). No build of the full workspace, no
`emit` run, no Lean invocation took place.

## 5. The runtime half lands — fisch re-run over emitted products (w05)

Date: `2026-09-11`. Base: `2fdded7`. Branch: `w05-zielschluss`.

Section 4 above booked the runtime half of
`messung/ABSENKUNG-ZAEHLUNG.md` section 2 as still missing. It landed
since: `messung/ABSENKUNG-LEXERLAUF.md` (lane 122, merged — seventeen
minimal units, one lexer, maximum seventeen confirmed over emitted
output) ran the procedure, and this section re-runs it on
`ki-pc-fisch-101` in the lane directory `gabbro-w05`, with a binary
built there from a clean tree. Nothing below changes a number: the
maximum stays `17`, the headroom stays `18`, and neither `Ziel.lean`
nor `absenkung.rs` moves. The bound is fixed accordingly — by
standing still, with the reason booked.

Provenance — what ran, on what base, from what tree:

```
git rev-parse HEAD
```

```
2fdded7360feafb659a6807eb9f73438ae9b34d7
```

```
git status --short
```

```
(empty — the worktree was clean before the transfer)
```

Transfer into the lane directory (code without timestamps, proofs
with them — the two-rsync rule from the work instructions):

```
rsync -rlpgoD --delete --exclude 'target/' --exclude '__pycache__/' --exclude '.claude/worktrees/' \
      ./ ki-pc-fisch-101:gabbro-w05/
rsync -a beweise/ ki-pc-fisch-101:gabbro-w05/beweise/
```

Build on the server (`cargo` off the server chain, output to a file —
no `pgrep -f` wait):

```
ssh ki-pc-fisch-101 'cd gabbro-w05 && export PATH=$HOME/.cargo/bin:$PATH && cargo build'
```

```
Finished `dev` profile [unoptimized + debuginfo] target(s) in 6.69s
```

The binary used for every emit below (built above, read-only
afterwards, no further `cargo` invocation):

```
gabbro-w05/target/debug/gabbro
```

Machine headroom beside the run (light emit runs only; the
heavy-build rule never came near):

```
free -g
```

```
               total        used        free      shared  buff/cache   available
Mem:             110          37           2           0          71          72
```

The units are the seventeen lane-122 files, unchanged
(`messung/proben/absenkung/probe-absenkung-*.gab`, one per `StmtArt`
variant, same scaffold — see `messung/ABSENKUNG-LEXERLAUF.md` section
2 for the scaffold, the two forced deviations, and the row
adjustments). The loop over all seventeen, with the server-built
binary:

```
for f in messung/proben/absenkung/probe-absenkung-*.gab; do
  ./target/debug/gabbro emit "$f" > /tmp/w05-absenk/out/$(basename "$f" .gab).c
  echo "$f exit=$?"
done
```

```
messung/proben/absenkung/probe-absenkung-awaitload.gab exit=0
messung/proben/absenkung/probe-absenkung-bricht.gab exit=0
messung/proben/absenkung/probe-absenkung-exchange.gab exit=0
messung/proben/absenkung/probe-absenkung-leave.gab exit=0
messung/proben/absenkung/probe-absenkung-let.gab exit=0
messung/proben/absenkung/probe-absenkung-letsonst.gab exit=0
messung/proben/absenkung/probe-absenkung-match.gab exit=0
messung/proben/absenkung/probe-absenkung-narrow.gab exit=0
messung/proben/absenkung/probe-absenkung-next.gab exit=0
messung/proben/absenkung/probe-absenkung-observiert.gab exit=0
messung/proben/absenkung/probe-absenkung-publish.gab exit=0
messung/proben/absenkung/probe-absenkung-return.gab exit=0
messung/proben/absenkung/probe-absenkung-ruf.gab exit=0
messung/proben/absenkung/probe-absenkung-schleife.gab exit=0
messung/proben/absenkung/probe-absenkung-sperrt.gab exit=0
messung/proben/absenkung/probe-absenkung-wenn.gab exit=0
messung/proben/absenkung/probe-absenkung-zuweisung.gab exit=0
```

The lexer is the lane-122 script verbatim (one `;` is one statement;
loop-header separators, comments, string/character literals
excluded; region from the main definition line to end of file;
`T` total, `V` parameter silencers, `R` return lines,
`P = T - V - R`), kept in lane scratch outside the tree
(`/tmp/w05-absenk/lexer.py`), one head line per output:

```
for f in /tmp/w05-absenk/out/probe-absenkung-*.c; do python3 /tmp/w05-absenk/lexer.py "$f" | head -1; done
```

```
probe-absenkung-awaitload.c: T=6 V=4 R=1 P=T-V-R=1
probe-absenkung-bricht.c: T=5 V=4 R=1 P=T-V-R=0
probe-absenkung-exchange.c: T=18 V=5 R=1 P=T-V-R=12
probe-absenkung-leave.c: T=8 V=4 R=1 P=T-V-R=3
probe-absenkung-let.c: T=7 V=4 R=1 P=T-V-R=2
probe-absenkung-letsonst.c: T=14 V=5 R=2 P=T-V-R=7
probe-absenkung-match.c: T=15 V=4 R=3 P=T-V-R=8
probe-absenkung-narrow.c: T=5 V=3 R=2 P=T-V-R=0
probe-absenkung-next.c: T=8 V=4 R=1 P=T-V-R=3
probe-absenkung-observiert.c: T=7 V=4 R=1 P=T-V-R=2
probe-absenkung-publish.c: T=6 V=3 R=1 P=T-V-R=2
probe-absenkung-return.c: T=5 V=4 R=1 P=T-V-R=0
probe-absenkung-ruf.c: T=6 V=4 R=1 P=T-V-R=1
probe-absenkung-schleife.c: T=20 V=2 R=1 P=T-V-R=17
probe-absenkung-sperrt.c: T=7 V=4 R=1 P=T-V-R=2
probe-absenkung-wenn.c: T=4 V=3 R=1 P=T-V-R=0
probe-absenkung-zuweisung.c: T=6 V=3 R=1 P=T-V-R=2
```

Every `T`/`V`/`R` figure agrees with
`messung/ABSENKUNG-LEXERLAUF.md` section 4 on its row — the lane-122
run used the main-tree prebuilt binary locally, this run a
server-built binary from a clean tree, and no row moves. The
per-row adjustments are lane-122's (same section: return reads `2`
across both frames, let-else `4`, match `8`, descendants traversal
`17`, leave/next `1` each past the carrier scaffold, publish `1`
past the writer store, exchange `10` past the nested body). The
maximum over all seventeen rows:

```
17
```

at `Schleife`, subform `traverse over descendants of` — the
seventeen emitted lines read exactly as booked there (root, cursor
and flag declarations, advance with flag reset plus `continue`,
loop-exit `break`, successor words, successor selection across both
branches, binder plus silencer, cursor writeback, trailing return).

Consequence for the bound: `17` fits `18` with the one headroom the
decision booked (`messung/ABSENKUNG-SCHRANKEN-ENTSCHEID.md`). The
constant in `grammatik/Grammatik/Ziel.lean`
(`⟨17, by decide⟩` under `≤ 18`) and the constants in
`crates/gabbro-check/src/absenkung.rs`
(`STATEMENTS_PER_PRIMITIVE = 18`, `MEASURED_MAXIMUM = 17`) already
say exactly this, so no file moves. A rise past `18` would move the
bound first in `Ziel.lean`, then in `absenkung.rs` — the order from
section 1 still stands.

## 6. The preservation leg — modeled ops keep the count (w05)

The numeric fragment (`absenkung_wert`, `absenkung_haelt_schranke`)
says the witness keeps the cap; it does not say lowering keeps the
`ops` count. The preservation theorem in `grammatik/Grammatik/Budget.lean`
(appended section `Lowering preservation for the modeled ops`,
additive — no existing line reworded, two import lines added,
`Grammatik.lean` untouched) says it for the modeled ops and reuses
the proved meaning leg instead of re-proving it:

```
modellKopf                          -- the seven CUT-1/2 heads read `true`
senkKosten                          -- one head lowers to one C-side op of cost 1
senkKosten_modell                   -- a modeled head costs exactly one C-side op
senkKosten_unter_schranke           -- that one op fits under the measured maximum
modell_erhaltung                    -- the preservation theorem: a valid modeled
                                       print elaborates (meaning, reused from
                                       `zeugnis_sound`) AND fits the max (count, new)
modell_lauf_erhalten                -- over modeled runs the lowered count IS the
                                       source count: one op in, one op out
```

The modeled heads are `sdiv`, `srem`, `band`, `bor`, `bxor`, `shl`,
`shr` — the CUT-1/2 certificate shapes whose range table and
soundness (`certRange`, `zeugnis_sound`) the `Zeugnis.lean` record
carries, with accept/reject `decide` probes beside them there and
here. The unmodeled remainder is named in the section header, not
dropped: the eleven other `CertExpr` heads (`lit`, `add`, `sub`,
`neg`, `mul`, `div`, `rem`, `wide`, `var`, `glob`, `slot`); the
CUT-3 shapes and the CUT-4/5 remainders (soundness proved in lane
106 as `cut3_sound`, `cut4_sound`, `block5_sound` — preservation not
stated); the `StmtArt`-level expansions above one statement (bounded
by section 5, enforced by `absenkung.rs` once the hook is applied,
no per-op preservation claim); and the C-to-Asm leg (`costKept`
CerCo implication, `costMeasured` production pairs in
`Erhaltung.lean` — untouched, Gabbro-to-C only here).

Checks, all on `ki-pc-fisch-101` in `gabbro-w05/grammatik` (server
Lean chain `~/.elan/bin`, release `4.33.1`, matching
`lean-toolchain`):

```
lake build
```

```
Build completed successfully (27 jobs).
```

```
lake env lean Grammatik/Budget.lean
```

```
exit=0
```

```
'Gabbro.Grammatik.modellKopf' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.senkKosten' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.senkKosten_modell' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.senkKosten_unter_schranke' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.modell_erhaltung' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.modell_lauf_erhalten' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The footprint is the standard one — the same three axioms the
neighbouring statement-threading section carries for mentioning
statements — and no new axiom: no `mathlib`, no `sorry`, no `axiom`.
The full-file check prints no `sorry`, no error, no warning beside
the twenty-three axiom lines.

No gift numbers were consumed: the run reused the seventeen
lane-122 units and the existing `TestD` probes, so `790`–`791` stay
free.

Evidence beside the run: the server build log (`cargo build`,
`Finished in 6.69s`), the seventeen `exit=0` emit transcripts, the
seventeen lexer head lines above (full per-line output in lane
scratch `/tmp/w05-absenk/out/`, kept off the tree), the `free -g`
table, the `lake build` log (`27 jobs`), and the `lake env lean`
log (`exit=0`, twenty-three axiom lines, six of them new).
