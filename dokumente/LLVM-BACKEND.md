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
`crates/gabbro-check/tests/llvm.rs` (14 tests, no external tool),
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

## 4. Measured snapshot 2026-10-14

Commands: `./target/debug/gabbro llvm`, `instrumente/baue-llvm.sh`,
`cargo test -p gabbro-check --test llvm`, `opt -O3` as IR *validator*
(compile-only — the validator adds nothing to any binary).

| | |
|---|---|
| Corpus lowered clean | 134 of 166 `beispiele/*.gab` (rest: named `Y` refusals, all booked open in `LLVM-MODELLSTAND.md`) |
| Clean IR valid for both targets | 134 of 134 (`opt -O3`, x86_64 + aarch64; arch-specific files correctly refused on the other target) |

| End to end, no libc | `messung/llvm/summe.gab`: checker green, static binaries, `OK`, rc=25 on **both** targets, agreement checked |
| Optimizer effect (`opt -O3` vs `-O0`, x86_64 native) | 20.3 ms → 3.3 ms (**6.2×**), identical output |
| `llc`-only `-O3` (no middle-end) | 43 ms — **slower than `-O0`**; `opt` belongs in the pipeline (measured, kept) |
| Binary size (static, summe) | 1848 bytes, no INTERP/NEEDED |
| IR size | 112 lines IR from ~60 lines Gabbro |
| Tests | 14 LLVM tests + full workspace suite green (incl. 5 `Y` probes) |
| New codes | `Y101`–`Y104` + `Y106` (emitter class, no sentences — `C001` precedent; `pruefe-saetze.py` mark 55 → 61 → 60: `Y105` retired, fully lowered; `Y106` narrowed to non-dispatched matches) |

Targets measured on unmatched settings are NOT reported: qemu timings are
emulation, and the Snapdragon device is pending — ARM performance is open
until hardware measures it (ARM-PLAN.md).

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
registers/bitfields/transitions (`volatile`, two sanctioned `inttoptr` sites),
tree walks (ancestors strict, descendants post-order stackless), `leave`/`next`
by name, atomic arrays.

Still refused, per item:

- IRQ-masking locks (`Y102`): need the interrupt model (which bit, nesting).
- Model registers/transitions (`Y10x`): the exporter builds no `Reg`; surface
  devices lower through `volatile`. A device state model is open work.
- Publish with payload (`Y103`): OFFEN O25, uncovered by the goal theorem.
- Shared locks (`Y103`): own primitive unproved — nothing serialized silently.
- Stack gates + `child` (`Y102`): need the `clone` trampoline.
- Entries (`Y102`, 12 sites): hardware dispatch (`unterbricht`).
- Table `ops` (`Y104`): generated mutators (the exporter has no G form either).
- `start`: lowers but runs SEQUENTIALLY (direct calls) — no real concurrency
  yet. The sharpest edge; everything else is refused by name or genuinely
  lowered.

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
- llvmArenen`: name, element layout, reservation, bound, ceiling (words at
  `<Name>.basis/.belegt/.bereit`); `llvmSchloesser`: ticket words at `<Name>`;
  `llvmFaeden`: roots (stacks/words at `gabbro_faden_N_*`).

The validator checks the final bytes against source plus this certificate.
Status: input to refinement, not a proof. A proved validator refuses bad
output; this file never grants it (§5).
