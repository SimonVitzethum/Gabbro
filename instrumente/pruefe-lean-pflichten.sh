#!/bin/bash
# **THE PERSON'S HALF, MEASURED** (2026-09-07) -- the tree-wide form of `gabbro prove`.
#
# `gabbro pflichten --lean` writes a unit's duties as `_statement`s and proves each with
# `gabbro_auto`, which leaves a `sorry` on what is the program's own logic. `gabbro prove`
# holds the OTHER file against it: `programmlogik/Proofs/<Unit>.lean`, written by a person,
# with one theorem per statement -- and it is green only when every statement of the unit
# has a proof there, and that proof uses no `sorry`.
#
#     unit.gab  ->  gabbro prove  ->  Duty/<Unit>.lean      (generated, never edited)
#                                     Proofs/<Unit>.lean    (written by a person)
#
# **The measurement lives in the checker (`gabbro_check::beweis`), not here** -- this
# script only runs it over a list of units and translates the exit code into the
# convention of this folder: 0 green, 1 the TREE has to change (a statement without a
# proof, a proof with a `sorry`, a red file), 2 the SETUP does (no binary, no Lean, the
# model does not build) -- nothing measured. `gabbro prove` says 3 for the setup case,
# because at its command line 2 is the unknown-command exit.
#
# `--vorlage <unit.gab>` prints the file a person starts from (`gabbro prove --template`).

set -uo pipefail

W="$(cd "$(dirname "$0")/.." && pwd)"
GABBRO="${GABBRO:-$W/target/debug/gabbro}"

if [ ! -x "$GABBRO" ]; then
    echo "LEAN DUTIES: NO GABBRO -- it is built on ki-pc-fisch-101 (CLAUDE.md)"
    exit 2
fi
if [ $# -eq 0 ]; then
    echo "usage: $0 [--vorlage] <unit.gab>..."
    exit 2
fi
if [ "${1:-}" = "--vorlage" ]; then
    shift
    "$GABBRO" prove --template "$@"
    exit $?
fi

"$GABBRO" prove "$@"
code=$?
case $code in
    0) echo "LEAN DUTIES: every statement has a proof without a \`sorry\`"; exit 0 ;;
    1) echo "LEAN DUTIES: a unit still owes something"; exit 1 ;;
    *) echo "LEAN DUTIES: nothing measured (no Lean, or the model does not build)"; exit 2 ;;
esac
