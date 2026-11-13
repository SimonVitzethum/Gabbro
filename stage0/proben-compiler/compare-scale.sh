#!/usr/bin/env bash
# Run under the repository's memory scope. No build: compare two already-built compilers.
# Usage: bash compare-scale.sh GEN-SCALE.SH BEFORE AFTER SCRATCH-DIRECTORY
# Measures wall time, exit status and image size; compares images and diagnostics exactly.
set -euo pipefail
generator=$(realpath "$1")
before=$(realpath "$2")
after=$(realpath "$3")
mkdir -p "$4"
scratch=$(realpath "$4")
export TMPDIR="$scratch"
exec 9>"$HOME/.cache/gabbro-stage0-build.slot-1.lock"
flock 9

generate() {
  bash "$generator" "$1" "$2" "$3" > /dev/null
}

measure() {
  local label=$1 binary=$2 name=$3
  shift 3
  free -g
  if ! awk '/MemAvailable:/ { exit !($2 >= 10 * 1024 * 1024) }' /proc/meminfo ||
      ! awk '{ exit !($1 <= 14) }' /proc/loadavg; then
    echo 'Insufficient available memory or load too high; retry later.' >&2
    exit 2
  fi
  local image="$scratch/$name.$label.img" started ended status
  rm -f "$image"
  started=$(date +%s.%N)
  if "$binary" --ir "$@" "$image" >"$scratch/$name.$label.stdout" \
      2>"$scratch/$name.$label.stderr"; then
    status=0
  else
    status=$?
  fi
  ended=$(date +%s.%N)
  printf '%s\n' "$status" >"$scratch/$name.$label.status"
  local bytes=0
  if (( status == 0 )); then bytes=$(wc -c < "$image"); fi
  awk -v name="$name" -v label="$label" -v rc="$status" -v start="$started" \
      -v end="$ended" -v bytes="$bytes" \
    'BEGIN { printf "%s\t%s\t%d\t%.6f\t%d\n", name, label, rc, end-start, bytes }' \
      >>"$scratch/results.tsv"
}

compare() {
  local name=$1 expected=$2
  shift 2
  measure before "$before" "$name" "$@"
  measure after "$after" "$name" "$@"
  cmp "$scratch/$name.before.status" "$scratch/$name.after.status"
  cmp "$scratch/$name.before.stdout" "$scratch/$name.after.stdout"
  cmp "$scratch/$name.before.stderr" "$scratch/$name.after.stderr"
  local status
  status=$(cat "$scratch/$name.before.status")
  if (( status == 0 )); then
    [[ $expected == accepted ]]
    cmp "$scratch/$name.before.img" "$scratch/$name.after.img"
  else
    [[ $expected == refused ]]
    [[ $status == 1 ]]
  fi
}

printf 'case\tcompiler\trc\twall_s\timage_bytes\n' >"$scratch/results.tsv"
# `plain` is a chain (one call per function). Keep a genuinely independent control
# to distinguish head-lookup costs from work proportional to the number of functions.
for kind in independent plain calls; do
  for count in 4000 8000 16000; do
    source="$scratch/$kind-$count.gab"
    generate "$kind" "$count" "$source"
    compare "$kind-$count" accepted "$source"
  done
done
for kind in longb longc; do
  for count in 1667 5000; do
    source="$scratch/$kind-$count.gab"
    generate "$kind" "$count" "$source"
    compare "$kind-$count" accepted "$source"
  done
done

# Each flat control contains exactly the declarations of its multi-module counterpart.
# Short names are globally distinct, so module key selection cannot introduce collisions.
for shape in 2:1000 8:250 8:1000; do
  files=${shape%:*}
  count=${shape#*:}
  name="modules-$files-$count"
  flat="$scratch/$name.flat.gab"
  printf 'module flat {\n' >"$flat"
  sources=()
  generate plain "$count" "$scratch/template.gab"
  for ((index=0; index<files; index++)); do
    source="$scratch/$name-$index.gab"
    awk -v tag="part$index" -v partIndex="$index" '
      {
        rest=$0; result=""
        while (match(rest, /p[0-9]+/)) {
          result=result substr(rest,1,RSTART-1) tag substr(rest,RSTART,RLENGTH)
          rest=substr(rest,RSTART+RLENGTH)
        }
        line=result rest
        sub(/module scale/, "module " tag, line)
        if (partIndex != 0) sub(/fn main\(/, "fn check" tag "(", line)
        print line
      }' "$scratch/template.gab" >"$source"
    sources+=("$source")
    sed '1d;$d' "$source" >>"$flat"
  done
  printf '}\n' >>"$flat"
  compare "$name" accepted "${sources[@]}"
  compare "$name-flat" accepted "$flat"
done

printf '%s\n' 'module refusal {' \
  'impl fn main() -> u32 in 0 .. 10 { return 7; }' \
  'impl fn main() -> u32 in 0 .. 10 { return 7; }' '}' >"$scratch/refusal.gab"
compare duplicate-function refused "$scratch/refusal.gab"
cat "$scratch/results.tsv"
