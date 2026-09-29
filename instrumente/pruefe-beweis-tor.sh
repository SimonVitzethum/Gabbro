#!/bin/bash
# The gates of `gabbro prove`, each with its poison probe (GabbroV lane, 2026-09-29).
#
# One unit (`beispiele/121-tagged-static-init.gab`, one duty `lies_meets_statement`), one
# proof that is GREEN, and one poison per gate. Every poison must be caught -- not GREEN, and
# with the exit code the verdict owes. Counts, never stops at the first failure.
#
#   gut          the positive control            GREEN  exit 0
#   sorry        a `sorry` in the proof          OWED   exit 1
#   fehlt        no proof file at all            OWED   exit 1
#   andere       a proof of ANOTHER statement    OWED   exit 1
#   axiom        an `axiom` of the person's      OWED   exit 1
#   native       `native_decide` inside          OWED   exit 1
#   name         the theorem has another name    OWED   exit 1
#   toolchain    a `lean` that does not run      SETUP  exit 3
#
# The model folder is a scratch folder of symlinks to `programmlogik/` with its OWN
# `Duty/` and `Proofs/`, so no run touches the checked-in model's generated files.
cd "$(dirname "$0")/.." || exit 2
G=${GABBRO:-target/release/gabbro}
[ -x "$G" ] || { echo "no $G -- cargo build --release first"; exit 2; }
free -g | sed -n 2p
W=.claude/muse-arbeit/kratz/beweis-tor
rm -rf "$W"; mkdir -p "$W/modell"
for e in programmlogik/* programmlogik/.lake; do
  case "$(basename "$e")" in Duty|Proofs|_pruefung) continue;; esac
  ln -s "$PWD/$e" "$W/modell/$(basename "$e")"
done
U=beispiele/121-tagged-static-init.gab
N=Duty121TaggedStaticInit
gut=messung/proben/beweis-tor/gut.lean
rot=0
probe() { # name, expected exit, expected word, [env]
  local name=$1 code=$2 wort=$3; shift 3
  local aus rc
  aus=$(env "$@" "$G" prove --model "$W/modell" "$U" 2>&1); rc=$?
  if [ "$rc" = "$code" ] && echo "$aus" | grep -q "$wort"; then
    echo "  ok   $name  ($wort, exit $rc)"
  else
    echo "  FAIL $name  expected $wort / exit $code, got exit $rc:"; echo "$aus" | head -6; rot=$((rot+1))
  fi
}
setze() { mkdir -p "$W/modell/Proofs"; cat > "$W/modell/Proofs/$N.lean"; }
kopf() { printf 'import Duty.%s\nset_option autoImplicit false\nopen Gabbro.Body GabbroDuty.%s\n\n' "$N" "$N"; }

setze < "$gut";                                              probe gut 0 GREEN X=1
sed 's/^  (obtain.*/  all_goals sorry/; /^  · exact/d' "$gut" | setze;  probe sorry 1 sorryAx X=1
rm -f "$W/modell/Proofs/$N.lean";                            probe fehlt 1 OWED X=1
{ kopf; echo 'theorem lies_meets_done : True := trivial'; } | setze;   probe andere 1 'no theorem' X=1
{ kopf; echo 'axiom cheat : lies_meets_statement'; echo 'theorem lies_meets_done : lies_meets_statement := cheat'; } | setze
probe axiom 1 cheat X=1
sed 's/^  unfold lies_meets_statement/  have _h : (2:Nat) + 2 = 4 := by native_decide\n  unfold lies_meets_statement/' "$gut" | setze
probe native 1 native_decide X=1
sed 's/lies_meets_done/lies_meets_bewiesen/' "$gut" | setze; probe name 1 'no theorem' X=1
setze < "$gut";                                              probe toolchain 3 SETUP LEANBIN=/bin/false
# the emitter's gate goes through the same measurement: C only for the GREEN proof
setze < "$gut"
"$G" emit --proved --model "$W/modell" "$U" 2>/dev/null | grep -q 'int main\|#include' && echo "  ok   emit-gut  (C written)" || { echo "  FAIL emit-gut: no C"; rot=$((rot+1)); }
sed 's/^  (obtain.*/  all_goals sorry/; /^  · exact/d' "$gut" | setze
if "$G" emit --proved --model "$W/modell" "$U" 2>/dev/null | grep -q '#include'; then echo "  FAIL emit-sorry: C was written"; rot=$((rot+1)); else echo "  ok   emit-sorry  (no C)"; fi
echo "poison probes not caught: $rot"
[ "$rot" = 0 ]
