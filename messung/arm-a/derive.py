import re, sys
src, dst, wt, gab = sys.argv[1:5]
L = open(src, encoding="utf-8").read().split("\n")
out = []
i = 0
# cut: Sprechprobe + FMA probe  (from LETZTE_STUFE="der Sprechprobe des Kopfes" up to 'schneide() {')
start = next(k for k, l in enumerate(L) if l.startswith('LETZTE_STUFE="der Sprechprobe'))
end = next(k for k, l in enumerate(L) if l.startswith('schneide() {'))
stop9 = next(k for k, l in enumerate(L) if l.startswith('LETZTE_STUFE="Stufe 9'))
L = L[:start] + L[end:stop9 - 1] + ['echo "ARM-PROBE-ENDE"', 'unset -f exit', 'builtin exit 0']
t = "\n".join(L)
t = t.replace("set -euo pipefail", "set -uo pipefail", 1)
t = re.sub(r'^W="\$\(cd .*$', 'W="%s"' % wt, t, count=1, flags=re.M)
t = t.replace('cargo run -q --manifest-path "$W/Cargo.toml" --bin gabbro --', '"%s"' % gab)
# lauf: wrap
t = t.replace("lauf() {          # $1 Name", "lauf_orig() {          # $1 Name", 1)
t = t.replace('echo "  5. -O2:        ok (gleiches Ergebnis wie -O0)"',
              'echo "  5. -O2:        ok (gleiches Ergebnis wie -O0)"\n    return 0', 1)
wrap = '''
lauf() {
    local n="$1"
    ( unset -f exit; set -e; lauf_orig "$@" ) > "$ARB/$n.protokoll" 2>&1
    local rc=$?
    if [ "$rc" = 0 ]; then echo "ARM-RESULT $n PASS"; else
        echo "ARM-RESULT $n FAIL rc=$rc :: $(grep -E 'GESCHEITERT|FALSCH|ANDERES|erzeugen|error' "$ARB/$n.protokoll" | head -1)"
        cp "$ARB/$n.protokoll" "$ARM_LOGDIR/$n.protokoll"
        [ -f "$ARB/ccfehler" ] && cp "$ARB/ccfehler" "$ARM_LOGDIR/$n.ccfehler"
        [ -f "$ARB/ccfehler2" ] && cp "$ARB/ccfehler2" "$ARM_LOGDIR/$n.ccfehler2"
    fi
}
exit() { echo "[exit $* suppressed outside a unit]"; return 0; }
'''
t = t.replace("N_DURCHGESTOCHEN=0\n", wrap + "N_DURCHGESTOCHEN=0\n", 1)
open(dst, "w", encoding="utf-8").write(t)
