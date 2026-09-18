# The user side of system calls — a construct, not a foreign body

*Written 2026-09-12. Design proposal; nothing here is built. Decision by Simon:
the user side of system calls gets explicit syntax, because it makes formally verified
standard libraries markedly cheaper.*

## 0. Why `extern fn` is not enough

Today a Gabbro program that calls an operating system writes a **foreign body**:

```gabbro
extern fn speicher_freigeben(p : Pa) effects { writes halde } costs <= 64 ops;
```

The contract is all Gabbro knows; that the OS keeps it is a named assumption
(`Hardware.annahme`). That stays correct, and for arbitrary foreign code it stays the form.
For a system call it throws away five things the call site actually knows:

| | what a system call has that a foreign body does not | what it buys |
|---|---|---|
| 1 | an **ABI**: call number, register binding, clobbers | the emitter writes the stub itself -- one template with one ruling in the `CForm` table instead of N hand-written `asm` blocks |
| 2 | a **structured error channel**: negative `rax` is an errno | decoded into the declared `or R` reasons, exhaustively; an errno outside the table is the named hardware outcome "the kernel answered outside its contract" |
| 3 | **OS state** the contract talks about: descriptors, offsets, mappings | ghost carriers in `effects`/`ensures` -- a buffered writer, an allocator or a file API becomes ordinary Gabbro code whose proof uses the syscall contracts |
| 4 | a **counterpart**: when the kernel is written in Gabbro (Caprock), its `entry syscall … dispatch` table entry for the same number | a declaration-level check that the user contract is implied by the kernel's proved contract -- the assumption at the boundary becomes a **theorem** |
| 5 | a **class** of assumption per call, with a falsifier probe, when the kernel is foreign (Linux) | the manifest lists every OS assumption by name, as it does for devices |

Item 4 is the one no comparable system has: SPARK, Cogent and Low\* all stop at the OS
boundary with an assumption. A Gabbro userland over a Gabbro kernel could close it.

## 1. Surface (proposal)

```gabbro
syscall write(fd : Fd, buf : ptr<normal, r> Bytes, len : u64 in 0 .. MAXLEN)
    -> u64 in 0 .. MAXLEN or IoError
    abi linux arch x86_64 number 1
    regs in  { rdi = fd, rsi = buf, rdx = len }
    regs out { rax }
    clobbers { rcx, r11 }
    errors   { EBADF => BadFd, EINTR => Interrupted, EAGAIN => WouldBlock }
    requires Open(fd)
    ensures  result <= len
    effects  { reads buf, writes os.fds }
    assume   linux_write_contract falsifier probe_write;
```

* `abi <name> arch <arch> number <n>`: the ABI table is a declaration (`linux`, `caprock`).
  `arch` is held against a declared `arch` (`A005`, as for `assume`). **x86_64 only** --
  `aarch64` stays sealed.
* `regs in`/`regs out`/`clobbers`: the mirror image of `entry` (`SYNTAX.md` §1, `entrydecl`),
  same checks (`G4`, `G7`).
* `errors`: a total map from the errnos the contract admits to the declared reasons. The
  decoding is generated; an unlisted errno is `hardware (annahme a)`.
* `assume … falsifier …` **or** `kernel <path>` (item 4): with `kernel`, the call is paired
  with a Gabbro kernel's dispatch entry and no assumption is named.

**Keyword.** `syscall` becomes a keyword. One corpus move: the entry name in
`beispiele/07-eintritt-und-boot.gab` (`entry syscall vector 0x80 …`) is renamed. The string
`"syscall"` inside the `asm` block of `beispiele/36-asm.gab` is untouched.

## 2. Meaning (Lean)

No new statement constructor. A `syscall` declaration is an `Ax` (`Syntax.lean`) with three
additions to `Deklaration`:

* `sysabi : Ax → Option SysAbi` -- number, register map, clobbers; consumed only by the emitter.
* the answer type of a syscall `Ax` is the sum `ok value | reason r`, filled by the generated
  errno decoding; `einpassen` holds the raw answer against it, as today for every axiom.
* ghost carriers for OS state (`os.fds`, …): tables the semantics treats like any carrier and
  the emitter omits. This is the `geist` flag of the reference branch
  `wip/maschine-pflicht-2026-09-11` (`Syntax.lean`, rule `G001`: executable code reads no
  ghost) -- to be ported, not reinvented.

**The pairing theorem (item 4)**, to be stated and proved:

> If a Gabbro kernel's dispatch entry for number `n` has a proved contract (requires `Pk`,
> ensures `Qk`, effects `Ek`), and the user-side `syscall` for `n` declares requires `Pu`,
> ensures `Qu`, effects `Eu` with `Pu → Pk`, `Qk → Qu`, `Ek ⊆ Eu` and the same register map,
> then the oracle premise `GutO` holds for that `Ax` -- the syscall needs no named
> assumption.

## 3. Build order (third wave, fixed statements per lane)

| # | lane | depends on |
|---|---|---|
| S1 | `SYNTAX.md` section plus guardians: vocabulary count (`pruefe-wortschatz.py`), grammar table, English guardian -- **patterns before the document moves** (`CLAUDE.md`) | -- |
| S2 | Lean: `SysAbi`, the errno sum as answer type, decoding totality theorem | -- |
| S3 | Lean: port the ghost-carrier flag from the reference branch; theorem that the emitted program never reads a ghost | -- |
| S4 | Lean: the pairing theorem of §2 | S2 |
| S5 | parser and checker: keyword, `abi`/`regs`/`errors` checks, the `kernel` pairing check (needs `cargo` on the build server, queued) | S1 |
| S6 | emitter: the stub template (inline `syscall`, register binding, clobbers) plus its ruling in the `CForm` table (`Erhaltung.lean`) | S5 |
| S7 | corpus: rename in `beispiele/07`; a new example -- a buffered writer over `write` whose flush is proved against the syscall contract; poison probes for a missing errno, a wrong register map, an arch mismatch | S5, S6 |

## 4. What this does NOT buy

* **The OS keeps its contract** stays an assumption whenever the kernel is not Gabbro.
  The construct names it per call; it does not discharge it.
* **Ghost OS state is a model.** That `os.fds` matches the kernel's real descriptor table is
  part of the assumption (foreign kernel) or of the kernel proof (Gabbro kernel).
* **Signals, `fork`, `mmap` of executable memory, `vfork`** change control flow or the
  address space under the caller; they are out of scope for this construct and stay foreign
  bodies until a separate design exists. **2026-09-18 (lane O-1, K-1): the thread-creation
  half of that exclusion is now a checked shape** -- `syscall … stack r` plus `child { … }`
  (`N446`-`N450`, emitter `C185`, model `CloneHandoff.lean`, premises (d)/(d2) of the goal;
  report `messung/muse/OPUS-BERICHT-CLONE.md`). The syscall to the OS stays user-made
  (numbers, registers, error maps never enter `crates/` or `grammatik/`); what is still
  missing is the lowering (inline trap, child entered by jump) and the stub correspondence
  lemma (§2 translation validation).
