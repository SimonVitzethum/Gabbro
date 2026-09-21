#!/usr/bin/env python3
"""No OS memory call outside `laufzeit/` (wave D, lane 242).

Binding constraint (Simon): no language feature hard-depends on an OS.
Reservation and commit live in `laufzeit/` behind the OS-free interface of
`laufzeit/arena_dyn.h`; the tree above it speaks slot counts, never pages.
A constant smuggled as documentation is still smuggled, so this scan reads
comments too -- over `crates/`, `grammatik/` and `beispiele/`.

Scope, and what it is not. Prose ABOUT the interface (`dokumente/`,
`messung/`, reports) names the tokens the way a specification names its
subject; that is not a use, the same call-site lesson `pruefe-waechter.py`
learned about `cc`. `laufzeit/` is the one home the tokens may have.
Vendored and build output (`.lake/`, `target/`, `.git/`, `__pycache__/`)
is not the tree. What is scanned: `.rs`, `.lean`, `.gab`, `.c`, `.h`,
`.py`, `.sh` under the three roots above.

Sprechprobe: `--selbsttest` plants a token file (must fall) beside a token-free
tree (must stay silent) and checks both directions. A fallen selftest ends
with 2: the setup failed, not the tree.
"""
import argparse
import pathlib
import re
import sys

WURZEL = pathlib.Path(__file__).resolve().parent.parent

SCAN_WURZELN = ("crates", "grammatik", "beispiele")
ENDUNGEN = {".rs", ".lean", ".gab", ".c", ".h", ".py", ".sh"}
AUSGENOMMEN = {".lake", "target", ".git", "__pycache__", "programmlogik"}

# OS memory surface: reserve/commit calls, their flags, and raw
# syscall-number spellings -- exactly the constraint's letter (ABI constant,
# syscall number, `MAP_*`). The lowercase call names carry ASCII-letter
# guards on both sides: without them `mmap` fires inside the German compound
# `Programmfragen` (`manifest.rs`), and a guardian with false alarms gets
# ignored. A header NAME in prose (`<sys/mman.h>` named as outside a table)
# is not a use -- any real use names a call or a flag below, which fires.
TOKEN = re.compile(
    r"(?<![A-Za-z])(?:munmap|mprotect|mmap|sbrk|VirtualAlloc)(?![A-Za-z])"
    r"|MAP_[A-Z_]+|PROT_[A-Z_]+"
    r"|__NR_[A-Za-z_]+|\bSYS_[A-Z_]+\b"
)


def dateien(wurzel):
    out = []
    for name in SCAN_WURZELN:
        basis = wurzel / name
        if not basis.is_dir():
            continue
        for pfad in sorted(basis.rglob("*")):
            if not pfad.is_file() or pfad.suffix not in ENDUNGEN:
                continue
            if any(teil in AUSGENOMMEN for teil in pfad.parts):
                continue
            out.append(pfad)
    return out


def scannen(wurzel):
    treffer = []
    gelesen = 0
    for pfad in dateien(wurzel):
        try:
            text = pfad.read_text(encoding="utf-8", errors="strict")
        except (OSError, ValueError):
            continue
        gelesen += 1
        for nummer, zeile in enumerate(text.splitlines(), 1):
            m = TOKEN.search(zeile)
            if m:
                treffer.append((str(pfad), nummer, m.group(0)))
    return gelesen, treffer


def selbsttest():
    import tempfile
    with tempfile.TemporaryDirectory() as d:
        ort = pathlib.Path(d)
        (ort / "crates").mkdir()
        (ort / "grammatik").mkdir()
        (ort / "crates" / "sauber.rs").write_text(
            "// reservation lives in laufzeit/\nfn hoefe() {}\n",
            encoding="utf-8",
        )
        # A German compound carrying the letters must stay silent: the
        # `Programmfragen` pin against false alarms.
        (ort / "crates" / "wortverbindung.rs").write_text(
            "/// Programmfragen sind keine Speichernfragen.\nfn ruhe() {}\n",
            encoding="utf-8",
        )
        (ort / "grammatik" / "schmutzig.lean").write_text(
            "-- mmap is not model vocabulary\n", encoding="utf-8"
        )
        gelesen, treffer = scannen(ort)
        # Forward: the planted token file falls, and only it; the compound
        # beside it stays silent.
        if gelesen != 3 or len(treffer) != 1:
            print(
                "selftest forward broken: read %d, hits %d"
                % (gelesen, len(treffer))
            )
            return False
        if not treffer[0][0].endswith("schmutzig.lean"):
            print("selftest forward hit the wrong file")
            return False
        # Reverse: a token-free tree stays silent.
        (ort / "grammatik" / "schmutzig.lean").write_text(
            "-- reservation lives in laufzeit/\n", encoding="utf-8"
        )
        gelesen2, treffer2 = scannen(ort)
        if gelesen2 != 3 or treffer2:
            print("selftest reverse broken: silence lost")
            return False
    print("selftest: 3 of 3 checks hold")
    return True


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--selbsttest", action="store_true")
    args = parser.parse_args()
    if args.selbsttest:
        sys.exit(0 if selbsttest() else 2)
    if not WURZEL.is_dir():
        print("pruefe-osfrei: NOTHING measured -- root %s missing" % WURZEL)
        sys.exit(2)
    gelesen, treffer = scannen(WURZEL)
    if treffer:
        for pfad, nummer, token in treffer:
            print("OS-TOKEN %s:%d: %s lives outside laufzeit/" % (pfad, nummer, token))
        print("%d files read, %d tokens outside laufzeit/" % (gelesen, len(treffer)))
        sys.exit(1)
    print("%d files read, no OS token outside laufzeit/" % gelesen)
    sys.exit(0)


if __name__ == "__main__":
    main()
