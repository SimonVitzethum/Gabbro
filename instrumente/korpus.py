#!/usr/bin/env python3
"""**Is this file one `git` knows about?** -- the one check a dozen walks were missing.

`messung/AUDIT-K100-2026-09-04.md` and `messung/K100-VERDICT-2026-09-04.md` found the
instance: `pruefe-sondendeckung.py`'s `korpus_dateien()` walked the working tree with
`pathlib.Path.rglob("*.gab")` and a hand-typed directory-name blacklist (`gift`, `.claude`,
`target`) that did not include `arbeitsprotokoll` -- so two UNTRACKED scratch files there
changed the guard's own population and made a speech test abort with `ABBRUCH`, not a
finding. `pruefe-unfalsifizierbar.py` carried the identical walk and the identical hole.

Adding `arbeitsprotokoll` to both lists fixed the INSTANCE. It did not fix the CLASS: a
directory-name blacklist only excludes the names someone has already been bitten by.
**The next untracked file just needs a different address** -- this module was written by
dropping one scratch `.gab` at the repository root (no `beispiele`, no `messung`, no
`arbeitsprotokoll`) and watching FIVE MORE instruments move: `pruefe-kennungen.py` flipped
an `ALL PASS` to a false double-issue from one untracked `.rs` under `crates/`, and
`miss-c-signaturen.py`'s own stated denominator ("`extern fn` at N distinct names") moved
from one untracked `.gab` under `beispiele/`. Neither directory was on any blacklist,
because neither had been the incident yet.

**The property that actually defines "part of the corpus" is not a location, it is
authorship: somebody `git add`ed the file.** `git ls-files` answers that directly, and a
blacklist of PLACES stops being able to run out of names.

USAGE -- one call added to an existing filter, not a rewrite of the walk
-------------------------------------------------------------------------
    import korpus                          # `instrumente/` steht in `sys.path[0]`

    return sorted(p for p in wurzel.rglob("*.gab")
                  if not {"gift", "target"} & set(p.relative_to(wurzel).parts)
                  and korpus.verfolgt(p, wurzel))

**Deliberately not a replacement for the directory filter.** Which directories to look
under, and whether `gift` (poison, tracked ON PURPOSE) belongs in or out, is a decision each
instrument already argues in its own comments -- `vergleiche-binaerprogramme.py` wants
EVERY `.gab` including poison, `pruefe-sondendeckung.py` wants the trust surface and not the
poison. Those decisions differ by design and stay where they are made. What every one of
them needs, and none should re-derive, is the answer to "is this an untracked file lying
around", and that is the one thing this module does.

**FAILS OPEN when `git` itself cannot answer, and says so once on stderr.** Measured while
building this module: a `git` WORKTREE (as opposed to a plain clone) rsynced to
`ki-pc-fisch-101` under `CLAUDE.md`'s own transfer recipe carries a `.git` FILE whose
`gitdir:` line is an ABSOLUTE path on the machine the worktree was created on --
`gabbro-schranke/.git` on the server read `gitdir: /home/…/Gabbro/.git/worktrees/agent-…`,
a path that does not exist there, so every command run there failed with the message
*"fatal: not a git repository"*. A filter that reads that failure as "nothing is tracked"
would turn every guardian built on this module into an empty-population pass
(`pruefe-sondendeckung.py` read **"0 von 0 emittierenden Dateien"** and a broken ratchet on
the first such run) -- the exact shape of finding this module exists to prevent, just moved
one level up. So when the underlying tool cannot be asked, `verfolgt()` returns `True` for
everything (the pre-existing behaviour, directory blacklist only) and prints ONE line to
stderr saying so -- a caller's own output contract is never a dependency's diagnostic to
break.
"""
import functools
import pathlib
import subprocess
import sys

_GEWARNT = set()


@functools.lru_cache(maxsize=None)
def _verfolgte_dateien(wurzel_aufgeloest: str):
    """The absolute paths `git ls-files` reports under `wurzel_aufgeloest`, or `None` if
    `git` itself could not answer -- cached once per root for the life of the process, a
    corpus walk asks this once per FILE and `git` should not run once per file."""
    try:
        r = subprocess.run(
            ["git", "-C", wurzel_aufgeloest, "ls-files", "-z"],
            capture_output=True, timeout=30,
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    if r.returncode != 0:
        return None
    wurzel = pathlib.Path(wurzel_aufgeloest)
    return frozenset(
        (wurzel / p).resolve()
        for p in r.stdout.decode("utf-8", "replace").split("\0")
        if p
    )


def verfolgt(pfad, wurzel) -> bool:
    """Is `pfad` a file `git` tracks in the checkout rooted at `wurzel`?

    A file `git add`ed but not yet committed still counts -- `git ls-files` reads the
    INDEX, and a staged file is exactly as much part of the corpus as a committed one. What
    it excludes is precisely what a directory blacklist cannot: a file nobody told git
    about, wherever it happens to sit.

    **Returns `True` (fails open) if `git` itself is unusable in this checkout** -- see the
    module docstring. That is strictly no worse than every walk's behaviour before this
    module existed, and reporting nothing tracked would be strictly worse.
    """
    wurzel_aufgeloest = str(pathlib.Path(wurzel).resolve())
    dateien = _verfolgte_dateien(wurzel_aufgeloest)
    if dateien is None:
        if wurzel_aufgeloest not in _GEWARNT:
            _GEWARNT.add(wurzel_aufgeloest)
            print(
                f"korpus.py: `git ls-files` failed under {wurzel_aufgeloest} -- "
                "falling back to the directory blacklist alone, untracked files included",
                file=sys.stderr,
            )
        return True
    return pathlib.Path(pfad).resolve() in dateien
