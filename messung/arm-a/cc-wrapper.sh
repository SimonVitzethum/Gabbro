#!/bin/bash
# cc wrapper for the AArch64 measurement: cross-compiles statically; if linking an executable,
# writes a shell launcher that runs the binary under qemu-aarch64. Sanitizer flags are dropped
# (no cross sanitizer runtime), and x86-only -m flags are dropped. Everything is logged.
args=(); out=""; link=1; prev=""
for a in "$@"; do
  case "$a" in
    -fsanitize*|-fno-sanitize*|-pthread|-mfma) continue;;
    -c|-S|-E) link=0;;
  esac
  if [ "$prev" = "-o" ]; then out="$a"; fi
  prev="$a"
  args+=("$a")
done
if [ "$link" = 1 ] && [ -n "$out" ]; then
  new=()
  skip=0
  for a in "${args[@]}"; do
    if [ $skip = 1 ]; then new+=("$out.a64"); skip=0; continue; fi
    if [ "$a" = "-o" ]; then new+=("-o"); skip=1; continue; fi
    new+=("$a")
  done
  aarch64-linux-gnu-gcc -static "${new[@]}"
  rc=$?
  if [ $rc = 0 ]; then
    printf '#!/bin/sh\nexec qemu-aarch64 %s.a64 "$@"\n' "$out" > "$out"
    chmod +x "$out"
  fi
  exit $rc
fi
exec aarch64-linux-gnu-gcc "${args[@]}"
