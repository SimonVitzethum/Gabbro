#!/usr/bin/env bash
# fein-suche.sh -- the witness search for the fine cells (CHECKER.md 16.8), as runs of the Lean driver `gen-fein`
# (grammatik/Grammatik/Gen/Fein/Lauf.lean). Every computation is the driver's; this script only starts it, in
# parallel and under a memory ceiling. The search is untrusted: every witness it prints is a program the kernel
# checks.
#
# The run cache. A run is (method, member source, member, body bound, expression fuel) and targets EVERY cell of the
# universe, so its result never depends on which cells are open and is computed once: messung/fein/laeufe/<run>.txt,
# one line `j cell cell ...` per packed program. A run that is in the cache is read, not computed again.
#
#   instrumente/fein-suche.sh bau
#       build `gen-fein` and copy it to target/fein/gen-fein (a later build does not disturb a running search)
#   instrumente/fein-suche.sh stufen METHODE Q A-B VON BIS EC SCHWELLE PAR
#       for every member A..B of source Q (m: `mitglieder`, f: `feinMitglieder`), PAR at a time: the runs at body
#       bounds VON, VON+1, ... BIS with expression fuel EC; the next bound only while the last run brought at least
#       SCHWELLE cells no cached run had (a large step is run only when the step before paid)
#       METHODE: gefiltert (novelty-filtered tables), voll (unfiltered, expressions bounded apart), vertreter
#       (representatives per own fine cells)
#   instrumente/fein-suche.sh deckung
#       the greedy cover by the cached programs: messung/fein/wahl.txt (`run j` per chosen program) and
#       messung/fein/offen.txt (the cells no cached program has)
#
# Memory: each driver process runs in a systemd scope with MemoryMax = min(FEIN_GB, available - 4) GB (default 8)
# and no swap; it does not start below 6 GB available. A scope that hits its ceiling ends that run only (the run is
# not cached and is tried again next time).
set -u
W=$(cd "$(dirname "$(realpath "$0")")/.." && pwd)
BIN=$W/target/fein/gen-fein
LAEUFE=$W/messung/fein/laeufe
mkdir -p "$LAEUFE"

deckel() {   # deckel COMMAND...: run COMMAND under the memory ceiling
  local want=${FEIN_GB:-8} avail lim
  avail=$(awk '/MemAvailable/ {print int($2/1048576)}' /proc/meminfo)
  if [ "$avail" -lt 6 ]; then echo "fein-suche: only ${avail} GB available, not starting" >&2; return 75; fi
  lim=$(( avail - 4 )); [ "$want" -lt "$lim" ] && lim=$want
  systemd-run --user --scope --quiet -p MemoryMax=${lim}G -p MemorySwapMax=0 -- nice -n 10 "$@"
}

case "${1:-}" in
  bau)
    (cd "$W/grammatik" && deckel env -u ELAN_TOOLCHAIN lake build gen-fein) || exit 1
    mkdir -p "$W/target/fein" && cp "$W/grammatik/.lake/build/bin/gen-fein" "$BIN" ;;
  stufen)
    [ $# -eq 9 ] || { echo "usage: $0 stufen METHODE Q A-B VON BIS EC SCHWELLE PAR" >&2; exit 2; }
    [ -x "$BIN" ] || { echo "no $BIN: run '$0 bau' first" >&2; exit 2; }
    m=$2 q=$3 a=${4%-*} b=${4#*-} von=$5 bis=$6 ec=$7 s=$8 par=$9
    export -f deckel; export BIN LAEUFE
    seq "$a" "$b" | xargs -P "$par" -I{} bash -c \
      "deckel \"\$BIN\" stufen $m $q {} $von $bis $ec $s \"\$LAEUFE\" 2>> \"\$LAEUFE/../log.txt\"" ;;
  deckung)
    [ -x "$BIN" ] || { echo "no $BIN: run '$0 bau' first" >&2; exit 2; }
    deckel "$BIN" deckung "$LAEUFE" "$W/messung/fein" ;;
  *)
    sed -n '2,32p' "$0"; exit 2 ;;
esac
