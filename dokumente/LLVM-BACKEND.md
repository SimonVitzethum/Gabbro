# LLVM backend: direct Gabbro → LLVM, without C anywhere

*Built 2026-10-14. Status: working pipeline incl. generated runtime, untrusted
compiler, checker first. No C in the pipeline: no C source, no C compiler, no
libc, no C runtime — and no linked runtime at all: locks, threads and arenas
are generated IR over raw kernel gates (the compiler does it, only the kernel
is underneath).*

## 1. What this is

A second producer beside the C producer (`emit.rs`): checked Gabbro lowers
**directly** to LLVM IR text (`.ll`), which the pure LLVM tools translate and link:

```
Gabbro --pruefe--> LLVM-IR --opt--> llc --> ld.lld --> static binary
```

The compiler is **untrusted** like the C one: the checker (`crate::pruefe`) runs
first, and what it refused never reaches this file as a green program. Every
unlowered form is refused **by name** (`Y101`–`Y106`, poison probes
`beispiele/gift/1427`–`1432`) instead of guessed — the `C001` rule.

Entry points: `gabbro llvm [--target=x86_64|aarch64] [--unit]` (IR to stdout),
`gabbro llvm-cert` (the Lean certificate for Gabbro→Binary refinement — same
run, NO LLVM inside, see §7), `instrumente/baue-llvm.sh` (end to end, both
targets, no-libc proof, agreement check). Tests:
`crates/gabbro-check/tests/llvm.rs` (IR tests without the LLVM toolchain),
`beispiele.rs` runs the LLVM emitter over the `Y` gift probes.

## 2. No C anywhere — how

| Step | Tool | C content |
|---|---|---|
| check + lower | `gabbro llvm` (this tree, `std` only) | none — writes IR text |
| middle-end opt | `opt -O3` (LLVM tool) | none |
| codegen | `llc -O3` (LLVM tool) | none |
| link | `ld.lld -static -e _start` | none — no objects, no start files |
| entry | `_start` emitted by the backend | calls `main`, exits via raw gate number |
| system calls | Gabbro `syscall` items with Gabbro register syntax | inline `syscall`/`svc` — no libc |
| runtime | none | binaries are static and freestanding |

`readelf` shows neither `INTERP` nor `NEEDED` — `baue-llvm.sh` checks this per
build (stage 4b). `clang`, `cc`, `gcc` never run; the script pins its exact
tool set (`$GABBRO`, `opt`, `llc`, `ld.lld`, `readelf`, `qemu-aarch64` for
execution only).

System calls lower from **direct gates**: explicit `number`, `regs in/out`,
clobbers, `abi linux`, matching `arch`, `via`-bound or direct, plain or
errno-decoded (`or R` channel). Handed stacks, kernel pairings and unbound
`via` gates stay refused (`Y102`).
Same-name gates with different `arch` coexist (the checker keys by `arch`);
the backend lowers the matching one and silently skips the other — a call with
no gate for the target refuses with `Y102` naming the architecture.
Programs with `extern` items still emit IR (with `declare`s), but the C-free
link finds no symbols for them — that boundary fails loudly at `ld.lld`, not
silently in the IR. The C-free script below accepts gate programs only.

## 3. Safety is preserved — by the checker, before a line of IR

The backend proves nothing itself; it preserves safety by **lowering only what
built passes decided**. Per lowered form (LLVM-0 fragment):

| Lowered form | Deciding pass (state) |
|---|---|
| ranges on integers, `narrow`, conversions | M1 + V1–V3 (**built**) |
| names, one declaration per place | Namen (**built**) |
| loops, `leave`/`next` targets, counted domains | M4/Schleifen (**built**) |
| tables/slots, `count` bounds, indices | M1 ranges + M4 domains (**built**) |
| `N411` integer-`match` coverage (our `switch` has no `default`) | intmatch refusal (**built**, fix lane F1) |
| gate numbers/registers (`N066` per-arch registers, `N464` length clause) | syscall rules (**built**) |
| effects/costs/contracts | erased — checked, not generated (CARRIED residues documented below) |

Measured on this tree: M1 reports **100 % typed expressions, 0 errors** on the
pure-Gabbro programs (`summe.gab`, hello-gate, string tests). What the checker
refuses never becomes IR — verified per file by `baue-llvm.sh` stage 1.

**What that does NOT say** (same honesty as the C backend): the 9 CARRIED
passes keep their named residues (alias analysis, `E010` reach, cost
assumptions, pairing memory-model statement). They concern contracts, costs and
proof duties — not the bytes' memory safety on this fragment, which the three
built passes carry. A green run is the absence of built-pass findings, not a
proof; the compiler stays untrusted and the proof is refinement (see §5).

## 4. Coverage and execution evidence (updated 2026-10-17)

Coverage is measured against Lean constructors/declaration fields, NEVER against
examples: `python3 instrumente/pruefe-llvm-modelldeckung.py` checks the explicit
register `dokumente/llvm-modelldeckung.tsv`. The model boundary and partial cases
are described in `LLVM-MODELLSTAND.md`. Counts of compilable examples are not a
completion metric.

Execution evidence is separate. The rule tests build and run both targets at
`-O0` and `-O3`: 200,000 non-tail calls on a 128 KiB native stack; indirect mutual
calls with aggregate returns and phi continuations; one-byte slot reuse; payload
page discard with preserved free links; checked static range zeroing; repeated
thread groups with a barrier requiring all roots to start before join. AArch64
execution uses qemu and is not a native performance measurement.

Historical optimization witness: `summe.gab` produced the same result at `-O0`
and `-O3`, with an earlier measured 20.3 ms -> 3.3 ms on x86-64. This is not a
comparison against GCC and not language-model coverage. The ARM 80 %/110 %
performance goals remain unmeasured.

## 5. What validating this would cost (evaluation, not a claim)

The asked question: what does it cost to translation-validate the LLVM path
(source → model → final bytes, checked in Lean)? Priced against the existing
C-chain experience (`zaehle-kette.py`: 2 of 129 chains closed; the sieves behind
it) and the new LLVM surface. Ranges, critical path first.

**The good news: the planned validator design does not change.** The selected
validation is source → final bytes with the middle untrusted
(`PLAN-UEBERSETZUNGSVALIDIERUNG.md` §§0–5): the Lean validator checks the
loaded image against the source-derived model, reusing W / GX for concurrency
plus the per-access target bridge. An LLVM middle-end is one more untrusted
byte producer beside the C one — it adds **no new proof architecture**, only
new surface in three places:

1. **Instruction semantics already covered.** The validator needs Armv9-A (+
   x86-64 while carried) instruction semantics either way — the Sail-based
   hardware model (`ARM-PLAN.md`) is the critical path and is shared with the
   native-compiler plan. LLVM adds nothing here: validated bytes are validated
   bytes, whichever tool wrote them.
2. **Two new machine forms: `syscall`/`svc` and the entry.** The validator must
   cover the raw gate instruction (register convention, answer register,
   clobbers, `memory`) and `_start` (stack, entry register state, exit /
   never-return). Small, closed, per-target: each is one correspondence lemma
   per gate shape, reusing the existing gate-contract form (`D.Ax`,
   `AufruferPflicht` vs `AxVertragOP`). Priced like the C stub lemmas (lane S6
   class): **1 lemma per gate shape + the entry lemma, per target**.
3. **The optimizer is the price driver — but it is priced per property, not per
   pass.** `opt -O3` runs dozens of passes; validating each is hopeless and
   unnecessary. What the validator checks is the *final bytes'* refinement of
   the source — vectorized or not, the bytes must simulate G/GX. The cost is:
   the per-access memory-model bridge (shared, see 1) + loop/assume reasoning
   strong enough to follow optimized code (induction over the lowered loops,
   `llvm.assume` facts as validator inputs). This is the same cost the native
   path pays for its own `-O3`-like optimizer — **no LLVM-specific surcharge
   beyond trusting nothing LLVM did**.

**Priced total (relative):** with the hardware model + final-byte validator in
place (the native plan's cost, unchanged), the LLVM path needs on top: gate +
entry lemmas per target (small, bounded — count the gate shapes, today: plain
call, `never` call, per arch), plus differential testing of the agreement
already automated here (`baue-llvm.sh` stage 5b extended per program). The
differential x86-64/aarch64 agreement in this pipeline is a standing
falsifier for backend bugs at zero proof cost.

**What is NOT claimed:** no validated binary exists today; `korrOk` is C-only;
the per-access target bridge is open; the 9 CARRIED checker residues stay out
of the binary-safety argument by the mapping in §3 (documented, not proved).
The validator, when built, refuses bad output — including ours.

## 6. Open (measured against the Lean model, not the corpus)

The measure is `dokumente/LLVM-MODELLSTAND.md`: every `Ty`/`Expr`/`Stmt`/`Block`
constructor and `Deklaration` field, booked LOWERED / REFUSED / ERASED / OPEN.
Lowered since LLVM-0 (each retired or narrowed its refusals; healed probes were
reclassified, never widened): variants (tag + payload bytes, constructors,
matches, bare cases), bounded strings (layout, literals, `lenof`, index, copy,
concat, lexicographic compare), the `or R` channel (fallible signatures,
`let … else` incl. option-index unpacking, reason values/matches, errno-gate
decoding, error propagation via `return e`), fn-pointers (`&f`, indirect calls
with declared signature), `retry` (counted bound, `bis` comparison, named
overrun handler), `breaking` (body runs), float ranges + runtime bounds in
`narrow`, `publish nothing` (release store), `await`/`exchange` (both forms),
option matches, float `finite`, sugar widths, `const fn` folding, device
registers/bitfields/transitions (`volatile`, three sanctioned `inttoptr` sites: device bases, region answers, arena runtime base),
tree walks (ancestors strict, descendants post-order stackless), `leave`/`next`
by name, atomic arrays, the unbounded heap with sampling (`pb P blw B`:
address-space reserve, per-MiB commit, one probe per commit, user threshold),
the slot release (`free A[i];`: LIFO reuse with separate metadata and static
death), and physical payload-page return. Runtime address conversions are
confined to declared devices/regions and compiler-owned mappings.

Still refused, per item:

- IRQ-masking locks (`Y102`): need the interrupt model (which bit, nesting).
- Model registers/transitions (`Y10x`): the exporter builds no `Reg`; surface
  devices lower through `volatile`. A device state model is open work.
- Publish with payload (`Y103`): OFFEN O25, uncovered by the goal theorem.
- Shared locks (`Y103`): own primitive unproved — nothing serialized silently.
- Stack gates + `child` (`Y102`): need the declared-gate/child integration;
  the internal `start` trampoline alone does not implement that source form.
- Entries (`Y102`): hardware dispatch (`Programm.unterbricht`).
- `start` now starts the whole group, joins after actual child exit and
  releases guarded per-invocation stacks. It no longer serializes the roots.
- General recursion, arena page return and static range reset are implemented;
  their remaining model/export and proof boundaries are in
  `LLVM-SPEICHER-STAPEL.md` and the checked model register.

## 7. The Lean certificate (`gabbro llvm-cert`)

Same checked unit, same lowering run as the IR — one run, two outputs (all maps
are `BTreeMap`: same source, same bytes, twice in a row). The file uses core
Lean syntax only (`def`, `structure`, `List`, `Option`, `String`, `Nat` — no
import, elaborates with plain `lean`) and carries **no LLVM** — refinement
Gabbro→Binary, never via intermediate text:

- `llvmEinheit/llvmZiel/llvmLayout`: what and for which target;
- `llvmFunktionen`: name, params, ret, linkage class;
- `llvmTypen`: named layouts;
- `llvmTore`: name, number, register bindings, out register, clobbers, template;
- `llvmEintritt`: `main` + width (or `never`);
- `llvmAnnahmen`: the `narrow` successes behind each `llvm.assume`;
- `llvmArenen`: name, element layout, reservation, bound, ceiling (runtime
  words: `<Name>.basis/.belegt/.bereit/.frei/.meta`); `llvmSchloesser`: ticket
  words at `<Name>`; `llvmFaeden`: roots owning guarded per-invocation regions.

The validator checks the final bytes against source plus this certificate.
Status: input to refinement, not a proof. A proved validator refuses bad
output; this file never grants it (§5).
