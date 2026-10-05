# MUSE-REPORT-1209: LOCK fetched-byte dispatch on the coherent machine

## Task
Follow-up of lane 1119 (`HwLockRmw.lean`): add fetched-byte dispatch on
`HwMaschine` for LOCK XADD/CMPXCHG/MFENCE, plus the narrower widths and
other addressing modes that `LockedInstructionExecution` (662) accepts,
and split-lock as a stated refusal. New file
`grammatik/Grammatik/X86/HwLockFetch.lean` + one import line in
`grammatik/Grammatik.lean`. No other file touched.

## What was done
New module `Gabbro.Grammatik.X86.HwLockFetch` (~660 lines), built in
small pieces, each `./lean-probe` checked, green partials committed
(4d810ba7, 456108a2, 30c3ab53, da7089fd).

- **§1 fetch**: `hwLockFetch m c := lockFetch (lockMaschineVonHw m c)` --
  the 662 fetch (actual executable bytes at the core RIP, combined
  decoder, length and execute-permission checks) on the core
  projection. No second fetch model (`hwLockFetch_aus_projektion`).
- **§2 split + step**: `cacheLinie = 64` (named assumption),
  `splitSperre` (8-byte word meets two lines), `lockFuss` (word
  footprint per form, `none` for MFENCE), `hwLockFetchSchritt`
  (fetch; parsed #UD refuses; split-lock words refuse; rest goes
  through the 1119 parsed plug), producer plug
  `adapterLockFetch : HwAdapter Unit` (the fetch decides, never the
  caller -- mirrors the 662 `lockByteschritt` discipline).
- **§3 equations + HwWf**: `hwLockFetchSchritt_ohne_fetch/_ud/_split/
  _ohne_split` and `adapterLockFetch_wf` (profiles untouched via the
  1119 re-embedding).
- **§4 discipline + bridge**: `hwLockFetch_weicht_aelter` (where
  `decodeExt` accepts, LOCK fetch refuses -- older rows keep bytes),
  `hwLockSchritt_trifft_byteschritt` and
  `hwLockFetchSchritt_trifft_lockByteschritt` (every admitted fetched
  step is a single-core 662 fetched `.ok` on the same projection).
- **§5 split pins**: crossing word at 8188 refuses the fetched step
  although the parsed plug would admit it; aligned 8192 never splits.
- **§6 widths/modes**: 32-bit (no REX.W), 16-bit (0x66 prefix) and
  mod=0 shapes have no fetched decode and refuse the step; the
  662-accepted SIB shape (10-byte XADD via rsp) dispatches and moves
  the word 10 to 15 (no shadowing by `decodeExt` -- decided, not
  assumed).
- **§7 two-core run**: fetched core-0 step equals the parsed step
  (word 10 to 15, rax 10, foreign buffer kept, owner-only
  forwarding); fetched core-1 step after the drain moves 15 to 22;
  fence advances RIP; pending own store, register-#UD, missing SSE2,
  unreadable word and misaligned base refuse on the fetched path.
- **§8 `hwLockFetch_zeuge`**: joint non-degenerate witness (two
  cores, memory-changing steps on both, forwarding, drain, SIB run,
  all refusals, `HwWf`).

## Verification
- `./lean-probe .../HwLockFetch.lean`: `== 0 error(s)`, exit 0.
- `./lean-bau`: `Build completed successfully (640 jobs)`.
- `#print axioms`: `propext` (+ `Quot.sound` where case analysis is
  used) -- standard set, no `sorry`/`admit`/`axiom`/`native_decide`/
  `unsafe`, English throughout. No `Prop`-typed premises; every
  premise is used (incl. the `Unit` plug token via the step
  hypothesis).

## What remains open / what I believe is correct but unproved
- Everything in the file's CUTS block: no hardware correspondence
  beyond 662 self-consistency; no W/GX refinement; narrower widths
  and further modes refused, not modelled; no timing/progress
  claims; no source/checker/goal change.
- Two deliberate non-claims: 64-byte lines and split-refusal are
  NAMED ASSUMPTIONS (no bus transaction performed, no #AC state
  claimed). I did not re-verify SDM Vol. 3A split-lock text in this
  lane (one read-only probe of the in-clone SDM text was blocked by
  the permission classifier); the assumption is stated, not cited.
- One mid-task correction worth knowing: the bridge block was first
  written before the equation lemmas (forward reference) and moved
  after them; plus a `rw`-after-`rw` that needed explicit `rfl`
  (reducible-transparency `rfl` does not iota-reduce `lockArt`).
  Both are fixed and green.

## Deliverable status
Complete: owned files are `grammatik/Grammatik/X86/HwLockFetch.lean`,
the one import line in `grammatik/Grammatik.lean`, and this report.
Full project build green.

## Integration gate failure -- analysis (repair turn, 2026-10-05)

The merge build failed with (verbatim):

> `error: Grammatik.lean:44:0: failed to read file
> '/home/simon/.elan/toolchains/leanprover--lean4---v4.33.1/lib/lean/Std/
> Tactic/BVDecide/Bitblast/BVExpr/Circuit/Impl/Operations/
> ZeroExtend.olean.private'`
> at step `[641/642] Building Grammatik`. Nothing was merged.

Finding, measured before the lane's shell access was revoked:

- My module compiled INSIDE the merge build: all 8 `info:` lines in
  the integration log are `HwLockFetch.lean` `#print axioms` outputs
  with the standard set (`propext`, `Quot.sound`). The failure is
  the step after, the final root `Grammatik.lean` link.
- The error is a file-READ failure of a toolchain installation
  artifact, not a Lean type error, not an axiom violation, not a
  missing or circular import. My diff introduces no new import
  (only `Grammatik.X86.HwLockRmw`, already in the tree) and no new
  toolchain dependency, so it cannot cause a missing
  `Std/...ZeroExtend.olean.private`.
- Local re-verification in clone a1209 at `424bd9b9`, clean tree:
  `./lean-probe grammatik/Grammatik/X86/HwLockFetch.lean` gives
  `== 0 error(s)`, exit 0; full `./lean-bau` gives
  `Build completed successfully (640 jobs)`.

Repair performed on owned files: NONE -- no source change exists
that addresses a missing toolchain file, and inventing one (e.g.
dropping stock `decide`, which the whole tree uses and which did
not cause this) would be churn, not a repair, and is refused under
the no-weakening rule. The module is unchanged since the accepted
isolated candidate.

Requested remedy, owned by the coordinator (outside lane scope, not
done here): verify/repair the `leanprover--lean4---v4.33.1`
toolchain installation serving the integration checkout
(`ZeroExtend.olean.private` present and readable; no concurrent
writer on shared toolchain/caches; see AGENTS.md section 9
apparatus notes), then re-run the merge gate on the UNCHANGED
candidate. A fresh independent review of the (unchanged) commit is
still required. No acceptance of the full source/binary chain is
claimed.

Blocker at report-writing time: lane shell access (`bash`,
therefore `./lean-probe` re-runs, `./commit.sh`, `git`) is refused
by the permission classifier, so this report update is written but
could not be committed from inside the lane. The working tree
contains exactly this file as the uncommitted change; everything
else is at committed `424bd9b9`, verified green as stated above.
