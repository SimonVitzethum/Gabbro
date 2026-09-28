# **WHICH `gabbro` BINARY -- and is it younger than the sources it claims to be?**
# (server lane, 2026-09-28. The shell half of the rule `pruefe-cformen.py` and
# `pruefe-saetze.py` already carry in Python.)
#
# THE TRAP, THREE TIMES IN ONE DAY. An instrument that takes
# `target/release/gabbro` because it exists measures whatever that binary was
# built from -- not the tree it is standing in:
#
#   * `pruefe-nebenlaeufig-zwilling.sh` reported the OLD `locks` lowering's
#     numbers against a tree whose emitter had already been repaired;
#   * `pruefe-kernelmodul.sh` built a module whose unit had no `GABBRO_ARENEN`
#     list yet, so NO arena was reserved and the first `grow` fell -- a red run
#     that said nothing about the tree;
#   * `miss-arena-decke.sh` measured the emitted C of an emitter that no longer
#     existed, and its GREEN said the ceiling costs nothing over the wrong bytes.
#
# *The same class as `rsync -a` against `cargo` (CLAUDE.md): a tool measuring a
# binary nobody built for it. And it is the WORSE direction of it -- there the
# build was a mixture, here the measurement is of something that is gone.*
#
# THE ANSWER, in one place because it was written three times: take the NEWER of
# the two profiles, and if any SOURCE of that binary is younger than it, say so
# and return 2. A binary older than a source is an ABORT, not a finding: nothing
# was measured, and a run that measured nothing is not a run that passed (`W1`).
#
# **AND A TEST FILE IS NOT A SOURCE OF THE BINARY** (server lane, 2026-09-28,
# the finding of session 6 repaired in session 10). The scan read every `*.rs`
# under `crates/`, so after any edit to `crates/*/tests/*.rs` every instrument
# answered `NOT RUN` -- and `cargo build --release` did NOT heal it, because it
# does not recompile the binary for a change to a separate test target. *A
# guardian that cannot be satisfied by doing the right thing is one whose word
# gets worked around*: it cost two full emission runs in session 6 and one more
# here, and the only healing was a `touch` on a source that had not changed.
# `tests/`, `benches/` and `examples/` are cargo's own separate targets and are
# excluded by path; everything else under `crates/` stays in, including a
# `build.rs` at a crate root, which IS an input.
#
# USAGE (two lines, and the caller keeps its own wording):
#
#     . "$(dirname "$0")/binaer.sh"
#     GABBRO="$(gabbro_binaer "$W")" || nicht_gelaufen "$GABBRO"
#
# On success it prints the path; on failure it prints the REASON, so the caller
# can hand it straight to its own "NOT RUN" line.
gabbro_binaer() {
    local w="$1" k="" neu=""
    for k in "$w/target/release/gabbro" "$w/target/debug/gabbro"; do
        [ -x "$k" ] || continue
        if [ -z "$neu" ] || [ "$k" -nt "$neu" ]; then neu="$k"; fi
    done
    if [ -z "$neu" ]; then
        echo "no built gabbro binary (cargo build)"
        return 2
    fi
    local juenger
    juenger="$(find "$w/crates" \
        \( -path '*/tests/*' -o -path '*/benches/*' -o -path '*/examples/*' \) -prune -o \
        -name '*.rs' -newer "$neu" -print 2>/dev/null | wc -l)"
    if [ "$juenger" != 0 ]; then
        echo "$neu is OLDER than $juenger source file(s) under crates/ -- build first"
        return 2
    fi
    echo "$neu"
}
