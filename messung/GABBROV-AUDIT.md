# GabbroV — the audit of Gate 2, of design C, and of the manifest

*Started 2026-09-03 from tree `393d866`. This file is the report, written as the run
proceeds and committed with each finding. Every count names the command that produced it.
This lane BUILDS nothing except where it says so at the site.*

**Machine note.** `free -g` beside every local run. Solver directory on the server would be
`gabbro-vm`, but see §0 — the solver is not there.

---

## 0. Two premises of the mandate, measured before anything was used

**`z3` is on THIS workstation and is NOT on `ki-pc-fisch-101`.** The mandate states the
opposite and it is the wrong way round.

```
which z3                        # no z3 in $PATH
/opt/verus/z3 --version         # Z3 version 4.16.0 - 64 bit
ssh ki-pc-fisch-101 'which z3; ls /opt/verus/z3'
                                # z3: command not found
                                # ls: cannot access '/opt/verus/z3': No such file or directory
```

So every solver call in this report is local, and that is not a breach of `CLAUDE.md`: a
`check-sat` on a 2–140 KB file is not a build. `free -g` at the start of the run reported
**31 GB total, 19 available**. The one call class that could have grown — the 60 s
reachability timeouts of §2.5 — was re-run with the memory watched.

*Reported rather than worked around, because a lane that quietly runs locally against an
instruction to run remotely leaves no record of which of the two was wrong.*

**The worktree was three commits behind `master` at start** (`01d69b2`), and none of the
five files the mandate names existed in it. `git merge --ff-only master` before the first
measurement, as `CLAUDE.md` requires. *A lane that measures a tree without the subject in it
gets a clean, meaningless zero.*

