# Lowering lexer run — per-primitive C statement counts from emitted output

Measured: the run below executed each unit in this record with the
main-tree prebuilt binary, counted the emitted C statements with the
documented lexer rule, and took the maximum over all primitives with
no early stop. The standing static count is seventeen; this run
confirms it as the maximum and raises one row beneath it.

## Zero. Verdict

The measured maximum over all primitives is:

```
17
```

It belongs to Schleife, subform traverse over descendants of, same
site as the static measurement. The static seventeen stands
confirmed. One row moves: Match measures eight against the static
five. The maximum does not move. No Lean source was touched and the
constant is unchanged; carrying the table into the counting file and
changing the constant were out of scope for this run.

## One. Provenance — what ran, on what base, with what headroom

The worktree stood on the lane base, branch lane-one-two-two, and the
checker sources were byte-identical to the base before the first emit.
The command and its (empty) output:

```
git diff --stat 58d6b83 -- crates/
```

```
(empty — no output, crates/ identical to the base)
```

The main tree, whose prebuilt binary this run used read-only, stood on
the same commit with clean checker sources:

```
git rev-parse HEAD
```

```
58d6b83963e3902183fd3762dca9a3be0d690921
```

The binary used, read-only, no build started, no cargo invocation:

```
/home/simon/Dokumente/Gabbro/target/debug/gabbro
```

Machine headroom beside the run (light emit runs only, each under a
second; the heavy-build rule never came near):

```
free -g
```

```
              gesamt       benutzt     frei      gemns.  Puffer/Cache verfügbar
Speicher:         31          14           3           2          15          16
Swap:              8           8           0
```

Measured on:

```
2026-09-11
```

## Two. The units — one per primitive, same scaffold each

Seventeen new units, one per variant of the statement enum, in the new
directory:

```
messung/proben/absenkung/
```

One file per primitive, same file scaffold in each: same module, same
declarations, same function signature, same effects clause. Only the
body differs, and each body exercises exactly its primitive. The file
names:

```
probe-absenkung-return.gab
probe-absenkung-ruf.gab
probe-absenkung-let.gab
probe-absenkung-letsonst.gab
probe-absenkung-zuweisung.gab
probe-absenkung-wenn.gab
probe-absenkung-match.gab
probe-absenkung-schleife.gab
probe-absenkung-bricht.gab
probe-absenkung-narrow.gab
probe-absenkung-sperrt.gab
probe-absenkung-observiert.gab
probe-absenkung-leave.gab
probe-absenkung-next.gab
probe-absenkung-publish.gab
probe-absenkung-awaitload.gab
probe-absenkung-exchange.gab
```

The shared scaffold carries every declaration any body needs: a tree
table with parent, child and sibling edges, a lock, a read-copy-update
domain with a reclaim place, two statics plus a report static, two
atomics (one releasing boolean, one relaxed counter), a two-case
reason, a two-variant tagged type, a memory-mapped device with a
fallible register and a read-write register with a one-bit field, one
assumption with its falsifier probe, three extern functions, and two
counterpart functions (one publishing writer, one awaiting reader) so
the pairing refusals of the checker have their unit-wide counterparts.
Every unit was diffed against the return unit; the only differences
are the header comment naming the primitive, the body line, and the
two forced deviations booked below.

Two deviations from one scaffold, both forced by named checker
refusals, both evidenced in the emit transcripts:

- The lock unit declares the taking in its effects clause; the other
  sixteen do not. A body that takes the lock without declaring it is
  refused, and a body that declares the taking without taking is
  refused. The emitted pre-body frame is byte-identical either way
  (measured — the pre-body hash below), so the clause never reaches
  the counted region.
- The let-else unit returns the error channel (`or` form of the
  signature); the other sixteen return a plain value. The fallible
  register read drops its error check without an error channel to
  carry it (measured — the plain-frame trial in section six), so the
  maximum path of this primitive needs the channel. The frame
  difference is the signature line and its out-parameters only, all
  pre-body.

Two facts about every body, both uniform, both part of the scaffold
for counting purposes:

- Every body ends with a value return. A body with no return at all
  under a value signature is refused by name (the no-return refusal),
  so the trailing return line belongs to the scaffold, not to any
  primitive. It contributes exactly one terminator in the plain frame
  and is subtracted from every row. The return unit is the special
  case: its exercised statement coincides with that line.
- Unused parameters lower to silencer lines, one per unused
  parameter, textually `(void)` plus the parameter name. They are
  scaffold and are subtracted per output as counted, never as
  assumed. Silencers over unit-local bindings (the loop binder, the
  unread let binder, the unread match payloads) are not parameters;
  they stay in their primitive row, as in the static measurement.

Every unit emitted with exit zero and non-empty C output. The loop
over all seventeen, run from the worktree root:

```
for f in messung/proben/absenkung/probe-absenkung-*.gab; do
  /home/simon/Dokumente/Gabbro/target/debug/gabbro emit "$f" > /tmp/absenk-lane122/$(basename "$f" .gab).c
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

The emitted pre-body frame (everything before the defined main body)
is byte-identical across the sixteen plain-frame units and the lock
unit:

```
bb9064915193c7b6c38583a449284558
```

The let-else unit differs only in the main signature and
out-parameter lines, all pre-body. The scaffold therefore cancels out
of the maximum as the procedure requires.

## Three. The lexer — the documented rule, as a command

One terminator in emitted C text is one statement, with three
exclusions: loop-header separators are not statements, comment text is
not statements, string and character literals are not statements. The
counted region starts at the main definition line and runs to end of
file (the defined main is last in every output). The script, kept in
scratch outside the tree so the tree carries only units and this
record:

```
import re, sys
src = open(sys.argv[1]).read()
src = re.sub(r'/\*.*?\*/', lambda m: '\n' * m.group(0).count('\n'), src, flags=re.S)
src = re.sub(r'//[^\n]*', '', src)
src = re.sub(r'"(\\.|[^"\\])*"', '""', src)
src = re.sub(r"'(\\.|[^'\\])*'", "''", src)
lines = src.split('\n')
pat = sys.argv[2] if len(sys.argv) > 2 else r'^static (?:uint32_t|bool) main\(.*\) \{$'
start = next(i for i, l in enumerate(lines) if re.match(pat, l))
body = lines[start:]
out = []
for l in body:
    j = 0
    while True:
        k = l.find('for', j)
        if k < 0 or not re.match(r'for\s*\(', l[k:]):
            break
        p = l.index('(', k)
        d = 0
        q = p
        while q < len(l):
            if l[q] == '(':
                d += 1
            elif l[q] == ')':
                d -= 1
                if d == 0:
                    break
            q += 1
        seg = l[p:q + 1].replace(';', ' ')
        l = l[:p] + seg + l[q + 1:]
        j = q + 1
    out.append(l)
body = out
T = sum(l.count(';') for l in body)
V = sum(l.count(';') for l in body if re.match(r'\s*\(void\)(d|b|s|w|n);', l))
R = sum(l.count(';') for l in body if re.match(r'\s*return .*;', l))
print(f"{sys.argv[1]}: T={T} V={V} R={R} P=T-V-R={T-V-R}")
for l in body:
    if ';' in l:
        print('   |' + l.strip())
```

Per output the lexer prints three counted figures and the row
arithmetic: total terminators in the region, terminators on
parameter-silencer lines, terminators on return lines. The row is the
total minus the two scaffold figures, plus the per-row adjustments
booked in section four, each with its emitting lines as evidence. One
booked correction during the run: the first revision blanked loop
headers with a paren-naive pattern that stopped at the first closing
paren inside size expressions and left one header separator counted;
the balanced-paren scan above replaced it, and the slot-traversal
trial moved accordingly (booked in section six).

## Four. Per-primitive rows — bodies, counts, adjustments

Each row names the unit file, shows the exercised body as written,
shows the lexer result over the emitted output, and books the row
with its adjustments. Row order follows the static table.

Return. The filed unit carries the plain return, which coincides with
the scaffold return line:

```
return n;
```

```
T=5 V=4 R=1 P=T-V-R=0
```

The formula reads zero because the single return line is both
scaffold and primitive. By inspection of that line the plain return
is one statement:

```
1
```

The error-channel return was measured on a trial unit under the error
frame (same lexer): the reason assignment plus the false return are
two statements:

```
2
```

The row is the maximum of the two paths:

```
2
```

Ruf. Body:

```
gib_art(); return n;
```

```
T=6 V=4 R=1 P=T-V-R=1
```

The row:

```
1
```

Let. Body (binding never read back, so the silencer fires):

```
let x : u32 = 1; return n;
```

```
T=7 V=4 R=1 P=T-V-R=2
```

The row (declaration plus silencer):

```
2
```

LetSonst. Body (fallible register read, error name used back in the
exit arm, value returned):

```
let t = d.TIEFE else (e) { return e; } return t;
```

```
T=14 V=5 R=2 P=T-V-R=7
   |(void)d;
   |(void)b;
   |(void)s;
   |(void)w;
   |(void)n;
   |(void)_grund;
   |uint32_t t;
   |Fehler e;
   |t = (*(volatile uint32_t *)(d.basis + 8));
   |e = Fehler_Leer;
   |*_grund = e;
   |return false;
   |*_wert = t;
   |return true;
```

Fourteen terminators minus five parameter silencers, minus the
emitter-added grund silencer line, minus two return lines, minus the
nested exit-arm lowering (the grund publish line), minus the trailing
value-out line, leaves binding declaration, error-name declaration,
single read, and reason materialisation:

```
4
```

Zuweisung. Body (register bit-field read-modify-write, the maximum
path):

```
d.QUIT.ACK = 1; return n;
```

```
T=6 V=3 R=1 P=T-V-R=2
```

The row (read plus write):

```
2
```

Wenn. Body (empty branches):

```
if w == 0 { } return n;
```

```
T=4 V=3 R=1 P=T-V-R=0
```

The row:

```
0
```

Match. Body (tagged scrutinee from a call, both payload binders
unread, every arm returning):

```
match gib_art() { A(x) => { return n; } B(y) => { return n; } } return n;
```

```
T=15 V=4 R=3 P=T-V-R=8
   |(void)d;
   |(void)b;
   |(void)s;
   |(void)w;
   |Art _m1 = gib_art();
   |uint32_t x = _m1.last.A;
   |(void)x;
   |return n;
   |} break;
   |bool y = _m1.last.B;
   |(void)y;
   |return n;
   |} break;
   |__builtin_unreachable();
   |return n;
```

Fifteen terminators minus four parameter silencers minus three return
lines (two arm returns plus trailing) leaves the temporary, two
payload declarations, two silencers, two breaks, and the unreachable
marker. The row:

```
8
```

This raises the static five, which counted one arm's worth of
payload, silencer and break. The raise moves no maximum.

Schleife. Body (descendants traversal, consuming run form, empty
nested body):

```
traverse opfer over descendants of b.slots[s] by consuming touches consumes b.slots { } return n;
```

```
T=20 V=2 R=1 P=T-V-R=17
   |(void)d;
   |(void)w;
   |const uint32_t _r1 = s;
   |uint32_t _k1 = _r1;
   |bool _h1 = false;
   |if (!_h1 && b->slots[_k1].kind != 8u) { _k1 = b->slots[_k1].kind; _h1 = false; continue; }
   |if (_k1 == _r1) break;
   |uint32_t _w1; bool _w1_hoch;
   |if (b->slots[_k1].schwester != 8u) { _w1 = b->slots[_k1].schwester; _w1_hoch = false; }
   |else { _w1 = b->slots[_k1].elter; _w1_hoch = true; }
   |const uint32_t opfer = _k1;
   |(void)opfer;
   |_k1 = _w1; _h1 = _w1_hoch;
   |return n;
```

Twenty terminators minus two parameter silencers minus the trailing
return leaves root, cursor and flag declarations (three), advance
with flag reset plus continue (three), loop-exit break (one),
successor word declarations (two), successor selection across both
branches (four), binder declaration plus silencer (two), and cursor
writeback (two). The row, and the maximum of the run:

```
17
```

Bricht. Body:

```
breaking kette_ruht { } return n;
```

```
T=5 V=4 R=1 P=T-V-R=0
```

The row:

```
0
```

Narrow. Body:

```
narrow w to 0 .. 100 else { return n; } return n;
```

```
T=5 V=3 R=2 P=T-V-R=0
```

The row (control structure and comments only):

```
0
```

Sperrt. Body:

```
locks SPERRE { } return n;
```

```
T=7 V=4 R=1 P=T-V-R=2
```

The row (take plus release):

```
2
```

Observiert. Body:

```
observes LESER { } return n;
```

```
T=7 V=4 R=1 P=T-V-R=2
```

The row (read-side enter plus exit):

```
2
```

Leave. Body (an endlessly labelled loop is the only legal carrier;
the checker refuses a jump with no enclosing label):

```
forever dienst per_pass bounded 64 ops on_exceeded aufgeben effects { pure } progress tickt { leave dienst; } return n;
```

```
T=8 V=4 R=1 P=T-V-R=3
   |(void)d;
   |(void)b;
   |(void)s;
   |(void)w;
   |static void (*const dienst_wachhund)(void) __attribute__((unused)) = aufgeben;
   |goto dienst_ende;
   |dienst_ende: ;
   |return n;
```

The jump line itself is the primitive. The row:

```
1
```

The remainder (watchdog line plus end-label null line) is the carrier
loop scaffold with its exit taken, booked here as orientation, not as
a row.

Next. Body (same carrier, the continue arm):

```
forever dienst per_pass bounded 64 ops on_exceeded aufgeben effects { pure } progress tickt { next dienst; } return n;
```

```
T=8 V=4 R=1 P=T-V-R=3
```

Same shape (watchdog line, jump line, start-label null line). The
row:

```
1
```

Publish. Body (the paired payload form; the checker refuses a payload
whose writer the function never reaches, so the plain store stands
beside the publish):

```
farbbericht = w; BEREIT = true publishes { farbbericht }; return n;
```

```
T=6 V=3 R=1 P=T-V-R=2
   |(void)d;
   |(void)b;
   |(void)s;
   |farbbericht = w;
   |atomic_store_explicit(&BEREIT, true, memory_order_release);
   |return n;
```

Six terminators minus three parameter silencers minus the trailing
return minus the writer store line (the assignment primitive, counted
on its own row) leaves the release store. The row:

```
1
```

AwaitLoad. Body:

```
let fertig = BEREIT awaits { farbbericht }; return n;
```

```
T=6 V=4 R=1 P=T-V-R=1
```

The row (no silencer fires on the await binder):

```
1
```

Exchange. Body (bounded update path, the maximum path; an empty
update body is refused by name, so the body returns its binder):

```
let alt = PEGEL exchange update(v) bounded N * 4 ops on_exceeded aufgeben { return v; } publishes nothing; return alt;
```

```
T=18 V=5 R=1 P=T-V-R=12
   |(void)d;
   |(void)b;
   |(void)s;
   |(void)w;
   |(void)n;
   |uint32_t alt;
   |uint32_t _ci1 = 0;
   |uint32_t _cx1 = atomic_load_explicit(&PEGEL, memory_order_relaxed);
   |uint32_t _cn1;
   |const uint32_t v = _cx1;
   |_cn1 = v; goto _cn1_fertig;
   |_cn1_fertig: ;
   |&PEGEL, &_cx1, _cn1, memory_order_relaxed, memory_order_relaxed)) break;
   |if (_ci1 >= (uint32_t)(N * 4)) { aufgeben(); }
   |_ci1++;
   |alt = _cx1;
   |return alt;
```

Eighteen terminators minus five parameter silencers minus the
trailing return minus the nested update-body lowering (the
two-terminator line carrying the body return) leaves binding
declaration, counter, expected-value load, operand declaration,
binder declaration, done-label null statement, break, bound-exit
call, counter increment, and result writeback. The row:

```
10
```

## Five. What the run says about the static seventeen

The maximum over all seventeen rows is the Schleife row:

```
17
```

It equals the static seventeen, measured independently through
emitted output rather than read off the emitter source. The standing
constant is confirmed, not raised, not methodologically disputed. Two
further bookings:

- The Match row measures eight against the static five and raises it.
  The static count booked one arm's payload declaration, silencer and
  break; an exhaustive match over two variants emits all three per
  arm. The raise moves no maximum.
- Every other row reproduces its static value exactly: two for
  return, assignment, let, lock-taking and the read side; four for
  let-else; ten for exchange; one for call, jump out, jump on,
  publish and await-load; zero for narrow, branch, breaking and the
  plain return path counted alone.

## Six. Tried alternatives — same lexer, scratch only, no files kept

While building the scaffold several neighbouring forms were measured
with the same lexer to make sure the filed body is each primitive's
maximum path. These ran as throwaway files in the main tree and were
removed afterwards; they are booked here so the choice of each filed
body is evidence, not taste.

- The plain-frame fallible register read (same let-else source under
  the plain value signature) drops the error check for lack of a
  channel and measures two (binding declaration plus single read).
  The filed error-frame unit measures four. The channel carries the
  check.
- The call-source let-else measures three (binding declaration,
  error-name declaration plus silencer, the call itself sitting in a
  branch condition with no terminator of its own).
- The payload-free publish measures one, same as the filed payload
  form. The filed form exercises the pairing; the count is the same.
- The plain assignment measures one against the filed bit-field
  read-modify-write at two.
- The option-form match measures two, same as its static value; the
  filed tagged form at eight is the row.
- The slot traversal measures zero direct (one loop header, no
  terminator), the bounded retry three, the endless loop one — all
  same as their static values; the filed descendants traversal at
  seventeen is the row.

```
2
```

```
3
```

```
1
```

```
1
```

```
2
```

```
0
```

```
3
```

```
1
```

In order: plain-frame let-else, call-source let-else, payload-free
publish, plain assignment, option match, slot traversal, bounded
retry, endless loop.

## Seven. What was expressly not done here

- No emitter or checker source was changed; no build started; no test
  suite ran. The binary was used read-only.
- No sentence in the language document, no fragment file, and no
  Lean source was changed — in particular not the lowering target
  file. The acceptance clause of the counting procedure names that
  file as the place where the maximum with its table lands; this run
  books the maximum and the table here, one step before it.
- The open fragment stands where the lowering record books it.
- The two forced scaffold deviations (lock effects on the lock unit,
  error frame on the let-else unit) and the two scaffold counterpart
  functions are booked in section two; the pre-body hash there shows
  the counted region is unaffected.
