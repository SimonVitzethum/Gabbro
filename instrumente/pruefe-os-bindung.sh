#!/usr/bin/env bash
# instrumente/pruefe-os-bindung.sh -- WHAT THE HOSTED RUNTIME TAKES FROM THE
# OPERATING SYSTEM, as a number that has to reach zero (server lane, TODO
# section 0e K8).
#
# THE QUESTION. Simon's binding constraint (2026-09-27) is *"API calls are always
# user-made"*, and on 2026-09-28 he drew the line for the runtimes too: *"an die
# Hardware ist OK, OS nicht, das muss selbst gemacht werden"* (`AUFTRAG-1.md`
# K8, acceptance point 4d). So: no OS call hard-wired in ANY runtime; the
# machine, on bare metal, is allowed. K7 did that for the module runtime and the
# stage `symbole_pruefe` of `instrumente/pruefe-kernelmodul.sh` is the number
# that said so (twelve kernel names, now 0). This instrument is the same
# measurement for the HOSTED runtime, and the same one turned around for the
# bare-metal one.
#
# THE CRITERION, PER OBJECT AND NOT PER BINARY, and that is the whole reason it
# can say anything. A hosted Gabbro binary names `printf`, `mmap` and
# `pthread_create` in one undefined-symbol list, and two of those three are the
# RUNTIME's while the first is the PROGRAM's -- `messung/proben/os-bindung/melde.c`
# calls it because `os-probe.gab` declared `gabbro_probe_melde` with its ABI, its
# effects, its cost and the assumption its body keeps. Nothing about the NAME
# tells them apart; the object holding the reference does:
#
#   * `nm -u <binary>`                      every libc/OS name the program still needs
#   * `nm -u` over the RUNTIME objects only (the generated `<unit>.treiber.c`,
#     `laufzeit/arena_dyn.c`, `laufzeit/faden.c`) -- what the runtime references.
#     The emitted unit is `#include`d into the driver, so the program's own
#     `extern fn` names are in there too; they resolve against the program's own
#     object and never reach the binary's undefined list, which is what the
#     intersection removes.
#   * the INTERSECTION, minus the toolchain's own names -> what the HOSTED
#     RUNTIME pulls out of the operating system.
#
# WHAT `nm` CANNOT SEE, AND WHY THERE IS A SECOND STAGE. `laufzeit/faden.c`
# issues `clone`, `futex` and `exit` as the `syscall` INSTRUCTION in inline
# assembly (lane 260: threads are made by our own code, not by libc), so it
# leaves no undefined symbol at all -- measured: `nm -u faden.o` is empty. A raw
# system call is an OS call even so, and `rohruf_pruefe` counts the sites in the
# hosted runtime's sources. Without it this instrument would report a hosted
# runtime that had merely hidden its Linux dependency in asm.
#
# AND THE THIRD STAGE IS THE ONE K8 ASKS FOR EXPLICITLY: bare metal calls no OS
# and never did -- what it hard-wires is the MACHINE (`outb`, `hlt`, `cli`/`sti`,
# `wrmsr`, `lidt`, the `lock`-prefixed instructions of the ticket lock), and that
# is allowed. `metall_pruefe` measures both halves of that sentence: no OS name
# in `laufzeit/metall/`, and how many machine accesses there are, so that the
# green says something instead of merely not saying no.
#
# A RATCHET, NOT A WALL -- for now, and the mark says which. The hosted runtime
# hard-wires twelve names today (the list is in the report, `messung/SERVER-0E-REPORT.md`
# section 14). A stage that demanded 0 before the work landed would be red on every
# run until it did, and *a red that says nothing new every time it is read is a
# red nobody reads.* So `MARKE_OSSYM` is the measured number, a run that needs
# MORE is refused -- and a run that needs FEWER is a finding too, the good case:
# the mark belongs pulled down. Exactly the shape `pruefe-emission.sh` uses for
# its emission counters and `pruefe-kernelmodul.sh` used before K7 landed.
#
# WHAT MAKES A GREEN RUN A MEASUREMENT -- the Sprechprobe of this instrument.
# `--gift N` mutates the harness or what it feeds the compiler, and the run must
# turn RED; `--gift all` runs every one and reports how many were caught. They
# are chosen so that no two are caught by the same stage.
#
# Missing `cc` or `nm` prints `OS-BINDUNG: NOT RUN` with the reason -- never a
# pass line. A binary older than the sources is the same: nothing was measured.
#
# Usage: instrumente/pruefe-os-bindung.sh [--gift N|all] [--keep]
set -u

# **The locale is pinned** (`pruefe-waechter.py`, requirement 5): this run reads
# the MESSAGES of `cc`, `nm` and the linker, and under `de_DE.UTF-8` the linker
# says `Mehrfachdefinition von` where the patterns below expect English.
export LC_ALL=C

W="$(cd "$(dirname "$0")/.." && pwd)"

# **Whoever leaves mid-run says WHERE** (`instrumente/abschnitt.sh`,
# `messung/RUECKLAUFWERTE.md`). This run has three exits that lie behind printed
# output and carry more output behind them -- the red verdict of the clean run,
# and `NOT RUN` from a missing tool or a stale binary. Without the notice each of
# them reads as a finding over the whole measurement instead of a cut through it.
. "$(dirname "$0")/abschnitt.sh"

GIFT=""
KEEP=0
while [ $# -gt 0 ]; do
    case "$1" in
        --gift) shift; GIFT="$1" ;;
        --keep) KEEP=1 ;;
        *) echo "pruefe-os-bindung.sh: unknown argument '$1'" >&2; exit 2 ;;
    esac
    shift
done

# -- the probe, and what it expects, in one place ------------------------------
#
# ONE probe, because one hosted program can ask the whole question: a
# `concurrent` set brings the generated driver (`pthread_create`, `pthread_join`,
# `main`), a `lock` brings its primitives (`pthread_mutex_lock`/`_unlock`), an
# `arena` with a ceiling brings `laufzeit/arena_dyn.c` (`mmap`, `mprotect`,
# `sysconf`), and one declared foreign function brings the PROGRAM's own libc
# call, which is the reference the criterion above has to NOT count.
#
# `laufzeit/faden.c` is linked in although this probe starts no `start`
# expression: it is a hosted runtime file, so it belongs in the measured set, and
# its contribution to the symbol stage is 0 by construction (raw syscalls, see
# `rohruf_pruefe`).
QUELLE="$W/messung/proben/os-bindung/os-probe.gab"
FREMD="$W/messung/proben/os-bindung/melde.c"
# **The binding, since K8's first slice** (2026-09-28): the probe declares an
# `arena`, and a hosted unit with an `arena` that binds no memory primitive is
# REFUSED by `gabbro build` before a byte of C (`bau.rs::bindungsregel_gehostet`).
# These two files are what the probe takes off the shelf -- ordinary user code in
# its manifest, like `melde.c` beside them -- and their object is the PROGRAM's,
# which is why `mmap`, `mprotect` and `sysconf` left the intersection below by
# the same move that made the runtime call them through declared names.
BINDUNG_GAB="$W/bibliothek/linux/linux.gab"
BINDUNG_C="$W/bibliothek/linux/linux.c"
EINHEIT="osprobe"

# **What the run must print**, and every line is a statement about the tree and
# not an observation of this machine:
#
#   k=2 v=32   every `alloc` of the growing root found room -- which it does only
#              if the arena was RESERVED before the roots started (the defect
#              this probe found, gift 5);
#   k=3 v=0    refuse-on-full was not reached; on hosted Linux the commit
#              practically always succeeds (OFFEN O20), and it is reported as
#              measured rather than assumed;
#   k=4 v=64   the sum over both roots under the one lock. The LAST of the two
#              reports stands after every increment either root made, whatever
#              the schedule, so this line must appear; the other `k=4` line is
#              between 32 and 64 and is not checked.
ERWARTET_BASIS="k=2 v=32
k=3 v=0
k=4 v=64"
ERWARTET="$ERWARTET_BASIS"

# **What the hosted runtime still takes from the OS: NOTHING.** Twelve when this
# stage was written on 2026-09-28, seven the same day, and **0 the day after**:
#
#   12 -> 7   the bounded heap's five (`mmap`, `mprotect`, `sysconf`, `exit`,
#             `fwrite`) left with `laufzeit/arena_dyn.c`, which calls the
#             program's binding now (`laufzeit/bindung.h`, `bibliothek/linux/`);
#    7 -> 0   the GENERATED DRIVER's seven (`pthread_create`, `pthread_join`,
#             `pthread_mutex_lock`, `pthread_mutex_unlock`, `pause` in the idle
#             root, `fprintf` and `abort`) left with the template
#             (`crates/gabbro-cli/src/treiber.rs`).
#
# **A ratchet at 0 is a wall**, and the stage stays written as a ratchet on
# purpose: a run that needs MORE is refused with the names it needed, and the
# reading of the number does not change when it reaches its floor. What it does
# NOT yet say is that the hosted runtime makes no system call at all -- the raw
# `clone`/`futex` of `laufzeit/faden.c` leave no symbol, and `MARKE_ROHRUF`
# below is where they are counted.
MARKE_OSSYM=0

# **How many raw system-call sites the hosted runtime issues.** Three call sites
# in `laufzeit/faden.c` (`clone` and the child's `exit` in `gabbro_faden_start`,
# `futex` in `gabbro_faden_warte` through `roh_aufruf`), and the numbers they
# pass. Counted as SITES of the `syscall` instruction, because that is the thing
# that reaches the kernel; the helper is one site even though two callers use it.
MARKE_ROHRUF=3

# The deadline for every step that executes something (`pruefe-waechter.py`,
# requirement 1). A hang is a finding here, not a state.
FRIST=300

# **The toolchain's own names, excluded because no program could declare them**
# -- the same list `pruefe-kernelmodul.sh` excludes, plus the hosted startup's.
OSSYM_TOOLKETTE='^(__fentry__|__x86_return_thunk|__stack_chk_|__ubsan_handle_|__sanitizer_|__gmon_start__|_ITM_|__libc_start_main|__cxa_|_init$|_fini$)'

# **The OS surface, by name, for the BARE-METAL stage.** What the machine layer
# must not call, because underneath it there is no operating system to answer:
# libc's process, memory, thread, printing and I/O calls.
#
# THREE FAMILIES ARE DELIBERATELY NOT IN IT, and each absence was a false alarm
# the first run produced:
#
#   * `memcpy`, `memset`, `memmove`, `strlen` -- a FREESTANDING C implementation
#     owes these to the compiler, and `laufzeit/metall/include/string.h` is where
#     the machine layer defines its own. They are not an OS interface; a compiler
#     emits calls to them for a struct assignment.
#   * `pause` -- on bare metal that is the `pause` INSTRUCTION in a spin loop
#     (the ticket lock's backoff), hardware and allowed. It is libc's
#     `pause(2)` only on the hosted side, where this stage does not look.
#   * anything in a COMMENT. Prose naming the token is not a use -- the lesson
#     `pruefe-osfrei.py` wrote down after `mmap` fired inside a German compound
#     -- and `laufzeit/metall/arena.c` explains in its header what it does
#     INSTEAD of `mmap`. Comment lines are dropped before the scan.
METALL_OS_NAMEN='(pthread_[a-z_]+|mmap|munmap|mprotect|sbrk|brk|malloc|calloc|realloc|printf|fprintf|sprintf|snprintf|puts|putchar|fputs|fwrite|fflush|exit|_exit|abort|sysconf|getpid|gettimeofday|clock_gettime|nanosleep|usleep|sleep|read|write|open|close|ioctl|socket|bind|listen|accept|send|recv|sendto|recvfrom|select|poll|epoll_[a-z]+|signal|sigaction|kill|fork|execve|waitpid|dlopen|dlsym)'

# **The machine, on bare metal, and it is ALLOWED** (K8's own sentence). These
# are instructions and MSR/port accesses, not API calls: counted so that
# "hardware only" is a number and not a claim.
METALL_HARDWARE='(\boutb\b|\binb\b|\boutl\b|\binl\b|\bhlt\b|\bcli\b|\bsti\b|\bwrmsr\b|\brdmsr\b|\blidt\b|\blgdt\b|\bcpuid\b|\brdtsc\b|\bpause\b|\bmfence\b|\block ;|lock cmpxchg|lock xadd|\bwbinvd\b|\binvlpg\b)'

nicht_gelaufen() {
    echo "OS-BINDUNG: NOT RUN -- $1"
    exit 2
}

# The notice is wired BEFORE the first thing that can leave, and the work
# directory does not exist yet -- so this trap carries no cleanup and is replaced
# by the one that does as soon as there is something to clean.
trap 'abschnitt_ende' EXIT
stufe_still "Kopf: Werkzeuge, Probe, Binaerprogramm"

for werkzeug in cc nm; do
    command -v "$werkzeug" >/dev/null 2>&1 || nicht_gelaufen "no $werkzeug on this machine"
done
[ -f "$QUELLE" ] || nicht_gelaufen "no probe source at $QUELLE"
[ -f "$FREMD" ]  || nicht_gelaufen "no probe C body at $FREMD"
[ -f "$BINDUNG_GAB" ] || nicht_gelaufen "no binding declarations at $BINDUNG_GAB"
[ -f "$BINDUNG_C" ]   || nicht_gelaufen "no binding bodies at $BINDUNG_C"

# **Which binary, and is it younger than the sources it claims to be?** One
# register, one file (`instrumente/binaer.sh`).
. "$(dirname "$0")/binaer.sh"
GABBRO="$(gabbro_binaer "$W")" || nicht_gelaufen "$GABBRO"

# -- the mutations (`--gift`) --------------------------------------------------
#
# Each one is a change to the harness or to what it hands the compiler, and each
# one must turn the run red. None of them touches the tree: every mutation is on
# a COPY in the work directory -- the same rule the module instrument keeps, and
# the reason two instruments can run beside each other.
#
#   1 the RUNTIME gains one OS call (`getpid()` in the generated driver's copy):
#     does the symbol stage see a call that arrived, or only the ones it knows?
#   2 the RUNTIME gains one RAW system call (a second `syscall` instruction in
#     the copy of `faden.c`): the stage `nm` is blind to, by construction.
#   3 the BARE-METAL runtime gains an OS call (`printf` in the copy of
#     `kern.c`): K8 allows the machine and not the OS, and this is the half that
#     says the difference is measured and not assumed.
#   4 the expected read-back moves (32 -> 33): does the run read the program's
#     output at all, or only the exit code?
#   5 the driver loses its ARENA RESERVATION (the block this session added):
#     without it `base` is NULL, every `grow` takes its `else`, and the heap is
#     DEAD -- silently, because refuse-on-full is a legal answer. *This is the
#     defect the probe found; the gift is what keeps it found.*
#   6 the BINDING leaves the manifest: the probe declares an `arena`, so
#     `gabbro build` must refuse it by name before a byte of C
#     (`bau.rs::bindungsregel_gehostet`). This is the half no `nm` could give --
#     a unit with no binding has no binary to measure, and what it would get
#     instead is the linker's "undefined reference to `gabbro_os_melden`",
#     about a name the program never wrote. The gift checks for the REFUSAL's
#     own sentence, because a build that failed for any other reason would turn
#     the run red through the wrong door.
#   7 the BINDING is declared with the WRONG ARITY (`gabbro_os_faden_start`
#     loses a parameter): C has no mangling, so a name of the right spelling and
#     the wrong shape LINKS and then reads a register nobody set. That is the
#     half of the rule a missing declaration never reaches
#     (`bau.rs::bindung_pruefe`), and it is checked by its own sentence too.
gifte() { echo "1 2 3 4 5 6 7"; }

# -- stage 1: build, link, run -------------------------------------------------
#
# `gabbro build` writes the emitted C and the driver; this harness compiles them
# and the runtime beside them. The driver is NOT compiled by the build (a
# deliberate split: it is the artefact the runtime half is run from), so the
# recipe below is this harness's -- and it is the same one the driver's own
# header comment prints.
bauen() {   # $1 = work dir, $2 = gift
    local arb="$1" gift="$2" bau="$1/bau"
    mkdir -p "$bau" "$arb/laufzeit"
    # The runtime sources are COPIED, because gifts 2 and 3 mutate them and the
    # tree is never written to by an instrument.
    cp "$W/laufzeit/arena_dyn.c" "$W/laufzeit/arena_dyn.h" "$W/laufzeit/bindung.h" \
       "$W/laufzeit/faden.c" "$W/laufzeit/faden.h" "$arb/laufzeit/"
    {
        echo "-- written by instrumente/pruefe-os-bindung.sh"
        echo "compiler cc -std=c11 -O0 -Wall -Wextra -Werror"
        echo "out $bau"
        echo "unit $EINHEIT object"
        echo "  $QUELLE"
        # **The DECLARATIONS are the unit's, the bodies are compiled by this harness**
        # -- which is what a driver written by hand does, and what every harness in
        # `instrumente/` does with the runtime beside it. The binding rule asks about the
        # declaration, so this is the whole of what the manifest needs.
        #
        # Gift 6 drops that line, and NOTHING else: the bodies still stand in the link, so
        # what the build refuses is the missing DECLARATION and not a missing file.
        if [ "$gift" = 7 ]; then
            echo "  $arb/linux-gift.gab"
        elif [ "$gift" != 6 ]; then
            echo "  $BINDUNG_GAB"
        fi
    } > "$arb/manifest"
    if [ "$gift" = 7 ]; then
        # The tree is never written to: the mutation is on a COPY, and its result
        # is checked rather than its intent.
        sed 's|^extern fn gabbro_os_faden_start(f : u64, koerper : u64) -> u32$|extern fn gabbro_os_faden_start(f : u64) -> u32|' \
            "$BINDUNG_GAB" > "$arb/linux-gift.gab"
        if ! grep -q '^extern fn gabbro_os_faden_start(f : u64) -> u32$' "$arb/linux-gift.gab"; then
            echo "HARNESS: gift 7 does not apply -- the declaration was not narrowed"
            return 0
        fi
    fi
    if ! timeout "$FRIST" "$GABBRO" build "$arb/manifest" > "$arb/bau.log" 2>&1; then
        if [ "$gift" = 7 ]; then
            if grep -q 'is bound with 1 parameter(s) and the runtime calls it with 2' "$arb/bau.log"; then
                echo "HARNESS: gift 7 -- the build refused the wrong arity by name"
            else
                echo "HARNESS: gift 7 does not measure -- the build failed for another reason"
                head -5 "$arb/bau.log" >&2
            fi
            return 0
        fi
        if [ "$gift" = 6 ]; then
            # **The refusal by its own sentence.** A build that failed for another
            # reason would turn this run red through the wrong door, and a gift caught
            # for the wrong reason is the trap this lane has paid for three times.
            if grep -q "binds no \`gabbro_os_" "$arb/bau.log"; then
                echo "HARNESS: gift 6 -- the build refused the unbound arena by name"
            else
                echo "HARNESS: gift 6 does not measure -- the build failed for another reason"
                head -5 "$arb/bau.log" >&2
            fi
            return 0
        fi
        echo "HARNESS: gabbro build FAILED"
        tail -20 "$arb/bau.log" >&2
        return 0
    fi
    if [ "$gift" = 6 ]; then
        echo "HARNESS: gift 6 does not measure -- the build ACCEPTED a unit with an \`arena\` and no binding"
        return 0
    fi
    if [ "$gift" = 7 ]; then
        echo "HARNESS: gift 7 does not measure -- the build ACCEPTED a binding of the wrong arity"
        return 0
    fi
    if [ "$gift" = 1 ]; then
        # One OS call more in the RUNTIME's own file. The driver includes no
        # system header any more (K8's second slice), so the gift brings its own
        # declaration -- which is the point: a call that compiles and links is
        # exactly the kind that arrives unnoticed, and a missing `#include` is
        # not what stops one.
        if ! grep -q '^int main(void)$' "$bau/$EINHEIT.treiber.c"; then
            echo "HARNESS: gift 1 does not apply -- no \`main\` in the driver"
            return 0
        fi
        sed -i 's|^int main(void)$|extern int getpid(void);\n\nint main(void)|' \
            "$bau/$EINHEIT.treiber.c"
        sed -i 's|^    uint32_t rc;$|    uint32_t rc;\n    (void)getpid();|' \
            "$bau/$EINHEIT.treiber.c"
        grep -q '(void)getpid();' "$bau/$EINHEIT.treiber.c" || {
            echo "HARNESS: gift 1 does not apply -- the call was not inserted"
            return 0
        }
    fi
    if [ "$gift" = 5 ]; then
        # The arena reservation goes, and nothing else. The mutation is on the
        # generated driver in the build directory, so the tree keeps its fix.
        if ! grep -q 'gabbro_arena_reserve(arenen\[a\]);' "$bau/$EINHEIT.treiber.c"; then
            echo "HARNESS: gift 5 does not apply -- the driver carries no arena reservation"
            return 0
        fi
        sed -i 's|            gabbro_arena_reserve(arenen\[a\]);|            (void)arenen[a];|' \
            "$bau/$EINHEIT.treiber.c"
    fi
    if [ "$gift" = 2 ]; then
        # A second `syscall` instruction in the copy of the thread runtime: one
        # more OS call the symbol stage cannot see.
        if ! grep -q '"syscall"' "$arb/laufzeit/faden.c"; then
            echo "HARNESS: gift 2 does not apply -- no \`syscall\` instruction in faden.c"
            return 0
        fi
        sed -i 's|^void gabbro_faden_warte(uint32_t \*wort)$|static long gabbro_gift_ruf(void)\n{\n    long r;\n    __asm__ __volatile__("syscall" : "=a"(r) : "a"(39L) : "rcx", "r11", "memory");\n    return r;\n}\n\nvoid gabbro_faden_warte(uint32_t *wort)|' \
            "$arb/laufzeit/faden.c"
        grep -c '"syscall"' "$arb/laufzeit/faden.c" | grep -qv '^1$' || {
            echo "HARNESS: gift 2 does not apply -- the second site was not inserted"
            return 0
        }
    fi
    local cflags="-std=c11 -O0 -Wall -Wextra -Werror"
    # The driver, with the emitted unit `#include`d into it.
    # `-I "$arb/laufzeit"` is what the driver needs since K8's second slice: it
    # `#include`s `bindung.h`, the interface it calls and does not define.
    if ! timeout "$FRIST" cc $cflags -I "$arb/laufzeit" -I "$bau" \
            -DEINHEIT_INCLUDE="\"$EINHEIT.c\"" \
            -c -o "$bau/treiber.o" "$bau/$EINHEIT.treiber.c" 2> "$arb/cc1.log"; then
        echo "HARNESS: the driver did not compile"
        head -20 "$arb/cc1.log" >&2
        return 0
    fi
    # The hosted runtime: the bounded heap and the threads. `-w` on the mutated
    # copy only, because gift 2's helper is deliberately unused.
    local rtflags="$cflags"
    [ "$gift" = 2 ] && rtflags="-std=c11 -O0 -w"
    if ! timeout "$FRIST" cc $rtflags -I "$arb/laufzeit" \
            -c -o "$bau/arena_dyn.o" "$arb/laufzeit/arena_dyn.c" 2> "$arb/cc2.log" \
       || ! timeout "$FRIST" cc $rtflags -I "$arb/laufzeit" \
            -c -o "$bau/faden.o" "$arb/laufzeit/faden.c" 2>> "$arb/cc2.log"; then
        echo "HARNESS: the hosted runtime did not compile"
        head -20 "$arb/cc2.log" >&2
        return 0
    fi
    # The PROGRAM's own C body, compiled on its own -- which is what makes its
    # `printf` the program's and not the runtime's in the measurement.
    if ! timeout "$FRIST" cc $cflags -c -o "$bau/fremd.o" "$FREMD" 2> "$arb/cc3.log"; then
        echo "HARNESS: the program's own C did not compile"
        head -20 "$arb/cc3.log" >&2
        return 0
    fi
    # **The binding is the program's too, and compiled as its own object** -- which is
    # the whole reason the measurement can tell its `mmap` from a runtime one. It reads
    # the runtime's interface (`-I "$arb/laufzeit"`) because that header is what holds
    # its six definitions against the declarations the runtime calls.
    if ! timeout "$FRIST" cc $cflags -pthread -I "$arb/laufzeit" \
            -c -o "$bau/bindung.o" "$BINDUNG_C" 2> "$arb/cc4.log"; then
        echo "HARNESS: the program's binding did not compile"
        head -20 "$arb/cc4.log" >&2
        return 0
    fi
    if ! timeout "$FRIST" cc -pthread -o "$bau/probe" \
            "$bau/treiber.o" "$bau/arena_dyn.o" "$bau/faden.o" "$bau/fremd.o" \
            "$bau/bindung.o" 2> "$arb/ld.log"; then
        echo "HARNESS: the linker refused the probe"
        head -20 "$arb/ld.log" >&2
        return 0
    fi
    echo "HARNESS: built ($(wc -l < "$bau/$EINHEIT.c" | tr -d ' ') lines of emitted C, $(wc -l < "$bau/$EINHEIT.treiber.c" | tr -d ' ') of driver)"
    local ist rc=0
    ist="$(timeout "$FRIST" "$bau/probe" 2> "$arb/lauf.err")" || rc=$?
    if [ "$rc" != 0 ]; then
        echo "HARNESS: the probe exited $rc"
        head -5 "$arb/lauf.err" >&2
        return 0
    fi
    printf '%s\n' "$ist" > "$arb/lauf.txt"
    echo "HARNESS: ran ($(grep -c '' "$arb/lauf.txt") reported line(s))"
}

# -- stage 2: the symbols the runtime pulls out of the OS ----------------------
symbole_pruefe() {   # $1 = work dir
    local arb="$1" bau="$1/bau" n
    [ -x "$bau/probe" ] || { echo "HARNESS: OS symbols NOT MEASURED -- no binary"; return 0; }
    nm -u "$bau/probe" | awk '{print $2}' | sed 's/@.*//' | sort -u > "$arb/bin.txt"
    nm -u "$bau/treiber.o" "$bau/arena_dyn.o" "$bau/faden.o" \
        | awk '/^ +U/{print $2}' | sed 's/@.*//' | sort -u > "$arb/rt.txt"
    comm -12 "$arb/bin.txt" "$arb/rt.txt" | grep -Ev "$OSSYM_TOOLKETTE" > "$arb/fest.txt"
    n="$(grep -c '' "$arb/fest.txt" | tr -d ' ')"
    if [ "$n" -gt "$MARKE_OSSYM" ]; then
        echo "HARNESS: OS symbols FAILED -- the hosted runtime hard-wires $n OS call(s), the mark is $MARKE_OSSYM"
        sed 's/^/    hard-wired: /' "$arb/fest.txt" | head -20
        return 0
    fi
    if [ "$n" -lt "$MARKE_OSSYM" ]; then
        echo "HARNESS: OS symbols FAILED -- the hosted runtime hard-wires $n, below the mark of $MARKE_OSSYM: the mark belongs pulled down (the good case, and a finding nonetheless)"
        return 0
    fi
    echo "HARNESS: OS symbols ok ($n hard-wired by the hosted runtime, mark $MARKE_OSSYM)"
    # The work quantity beside the verdict (`pruefe-waechter.py`, requirement 4):
    # a green over an empty set is a green over nothing.
    echo "HARNESS: read $(grep -c '' "$arb/bin.txt") binary symbol(s) against $(grep -c '' "$arb/rt.txt") runtime reference(s)"
}

# -- stage 3: the raw system calls `nm` cannot see -----------------------------
rohruf_pruefe() {   # $1 = work dir
    local arb="$1" n
    n="$(grep -c '"syscall' "$arb/laufzeit/faden.c" "$arb/laufzeit/arena_dyn.c" 2>/dev/null \
        | awk -F: '{s+=$2} END {print s+0}')"
    if [ "$n" -gt "$MARKE_ROHRUF" ]; then
        echo "HARNESS: raw syscalls FAILED -- the hosted runtime issues $n, the mark is $MARKE_ROHRUF"
        grep -n '"syscall' "$arb/laufzeit/faden.c" "$arb/laufzeit/arena_dyn.c" 2>/dev/null \
            | sed "s|$arb/||" | sed 's/^/    raw: /' | head -10
        return 0
    fi
    if [ "$n" -lt "$MARKE_ROHRUF" ]; then
        echo "HARNESS: raw syscalls FAILED -- the hosted runtime issues $n, below the mark of $MARKE_ROHRUF: the mark belongs pulled down (the good case, and a finding nonetheless)"
        return 0
    fi
    echo "HARNESS: raw syscalls ok ($n site(s) of the \`syscall\` instruction, mark $MARKE_ROHRUF -- K8's remaining mark)"
}

# -- stage 4: bare metal is OS-FREE, and the machine is allowed ----------------
#
# WHAT THIS MEASURES AND WHAT IT DOES NOT. The metal image is linked `-nostdlib`
# with no C library at all (`bau.rs::METALL_FLAGGEN`), so an OS name it
# referenced would be a LINK error and `instrumente/pruefe-freistehend.sh` would
# already be red. What that link cannot show is a name the runtime DEFINES
# itself -- its own `printf`, its own `malloc` -- which links perfectly and is
# still an OS interface growing inside the machine layer. That is the half this
# stage reads, over the source, and it says so rather than implying more.
#
# The scan itself is one function so that the stage and its poison run read the
# SAME code over different trees -- a gift whose check is a second copy of the
# check measures the copy (`W7`).
metall_os_funde() {   # $1 = directory; prints `file:line:name` per finding
    grep -rn --include='*.c' --include='*.h' --include='*.S' -E \
        "(^|[^A-Za-z_])$METALL_OS_NAMEN[[:space:]]*\(" "$1" 2>/dev/null \
        | grep -Ev '^[^:]+:[0-9]+:[[:space:]]*(\*|//|/\*|#[[:space:]])' \
        | sed "s|^$1/||"
}

metall_pruefe() {   # $1 = work dir
    local arb="$1" dir="$1/metall" n hw dateien
    mkdir -p "$dir"
    cp -r "$W/laufzeit/metall/." "$dir/"
    n="$(metall_os_funde "$dir" | grep -c '' | tr -d ' ')"
    hw="$(grep -rhEo --include='*.c' --include='*.h' --include='*.S' "$METALL_HARDWARE" "$dir" 2>/dev/null \
        | grep -c '' | tr -d ' ')"
    dateien="$(find "$dir" -type f \( -name '*.c' -o -name '*.h' -o -name '*.S' \) | grep -c '' | tr -d ' ')"
    if [ "$n" != 0 ]; then
        echo "HARNESS: bare metal FAILED -- the machine layer names $n OS call(s), and K8 allows the machine and not the OS"
        metall_os_funde "$dir" | sed 's/^/    OS in /' | head -10
        return 0
    fi
    echo "HARNESS: bare metal ok (no OS call in $dateien file(s) of the machine layer; $hw machine access(es) -- port I/O, hlt, cli/sti, MSRs, the ticket lock's locked instructions -- and those are allowed)"
}

beurteile() {   # $1 = output file, $2 = gift
    local aus="$1" gift="$2" fehler=0
    if grep -q "HARNESS: .*FAILED" "$aus"; then
        echo "RED: a stage of the measurement fell:"
        grep "HARNESS: .*FAILED" "$aus" | sed 's/^/     /'
        grep "^    hard-wired: \|^    raw: \|^    OS in " "$aus" | head -8 | sed 's/^/     /'
        fehler=$((fehler+1))
    fi
    for schritt in "built" "ran"; do
        if ! grep -q "HARNESS: $schritt" "$aus"; then
            echo "RED: the probe was not $schritt"
            fehler=$((fehler+1))
        fi
    done
    if grep -q "HARNESS: OS symbols NOT MEASURED" "$aus"; then
        echo "RED: the symbol stage had no binary to read -- nothing was measured"
        fehler=$((fehler+1))
    fi
    # **The run's own answer, line by line.** A missing line is a finding of its
    # own: the numbers are what make the build a program and not an artefact.
    if [ -f "${aus%/aus.txt}/lauf.txt" ]; then
        while IFS= read -r zeile; do
            [ -n "$zeile" ] || continue
            if ! grep -Fqx "$zeile" "${aus%/aus.txt}/lauf.txt"; then
                echo "RED: the run did not report \`$zeile\`"
                sed 's/^/       got: /' "${aus%/aus.txt}/lauf.txt" | head -8
                fehler=$((fehler+1))
            fi
        done <<EOF
$ERWARTET
EOF
    fi
    [ -n "$gift" ] || true
    echo "FEHLER=$fehler"
}

ARB="$(mktemp -d "${TMPDIR:-/tmp}/gabbro-osbindung.XXXXXX")"
# **`abschnitt_ende` runs FIRST in the trap**, because it reads `$?`.
if [ "$KEEP" = 0 ]; then
    trap 'abschnitt_ende; rm -rf "$ARB"' EXIT
else
    trap 'abschnitt_ende' EXIT
fi

einmal() {   # $1 = work dir, $2 = gift  -- every stage runs, none aborts the next
    local arb="$1" gift="$2"
    # **Every per-run variable is reset first, and this line is not decoration.**
    # Gift 4 moves the EXPECTATION, and without the reset it moved it for gift 5
    # as well: the first full run reported gift 5 as *"did not report `k=2 v=33`"*
    # -- caught, and for the wrong reason. *A selector that only ever SETS
    # carries the last probe's answer* (`~/claude-lane/STAND.md`, and the same
    # trap `probe_waehle` in `pruefe-kernelmodul.sh` already paid for).
    ERWARTET="$ERWARTET_BASIS"
    if [ "$gift" = 4 ]; then
        # **The expectation moves, and nothing else.** A harness that only read
        # the exit code would stay green: the probe answers 0 either way, and the
        # numbers are the whole reason it is a program and not an artefact.
        # *A `sed` that matched nothing says nothing*, so the result is checked
        # and not the intent.
        local vorher="$ERWARTET"
        ERWARTET="$(printf '%s\n' "$ERWARTET" | sed 's/^k=2 v=32$/k=2 v=33/')"
        if [ "$ERWARTET" = "$vorher" ]; then
            echo "HARNESS: gift 4 does not apply -- the expectation carries no \`k=2 v=32\` line"
        else
            echo "HARNESS: gift 4 -- the expectation now demands \`k=2 v=33\`"
        fi
    fi
    bauen "$arb" "$gift"
    symbole_pruefe "$arb"
    rohruf_pruefe "$arb"
    if [ "$gift" = 3 ]; then
        mkdir -p "$arb/metall"
        cp -r "$W/laufzeit/metall/." "$arb/metall/"
        if ! grep -q 'void metall_schreibe' "$arb/metall/kern.c"; then
            echo "HARNESS: gift 3 does not apply -- no metall_schreibe in kern.c"
        else
            sed -i 's|^void metall_schreibe|static void gabbro_gift_os(void) { printf("x"); }\n\nvoid metall_schreibe|' \
                "$arb/metall/kern.c"
            grep -q 'printf("x")' "$arb/metall/kern.c" \
                || echo "HARNESS: gift 3 does not apply -- the OS call was not inserted"
        fi
        # The stage reads the copy the gift just wrote, not a fresh one -- and it
        # reads it with the SAME function the clean stage uses.
        local n
        n="$(metall_os_funde "$arb/metall" | grep -c '' | tr -d ' ')"
        if [ "$n" != 0 ]; then
            echo "HARNESS: bare metal FAILED -- the machine layer names $n OS call(s), and K8 allows the machine and not the OS"
        else
            echo "HARNESS: bare metal ok (nothing found -- and the gift was supposed to plant something)"
        fi
    else
        metall_pruefe "$arb"
    fi
}

if [ -z "$GIFT" ]; then
    stufe_still "der saubere Lauf (bauen, Symbole, Rohrufe, Metall)"
    echo "== What the hosted runtime takes from the operating system =="
    echo "   probe       $QUELLE"
    echo "   own C       $FREMD"
    echo "   runtime     laufzeit/{arena_dyn.c,faden.c} + the generated $EINHEIT.treiber.c"
    mkdir -p "$ARB/lauf"
    einmal "$ARB/lauf" "" > "$ARB/lauf/aus.txt"
    grep -E "HARNESS:|^    " "$ARB/lauf/aus.txt" | sed 's/^/   /'
    ergebnis="$(beurteile "$ARB/lauf/aus.txt" "")"
    echo "$ergebnis" | grep -v '^FEHLER=' || true
    n="$(echo "$ergebnis" | sed -n 's/^FEHLER=//p')"
    echo
    if [ "$n" = 0 ]; then
        echo "GREEN: the hosted runtime names $MARKE_OSSYM operating-system function(s) of"
        echo "       its own; its raw system calls are COUNTED at $MARKE_ROHRUF, which is the"
        echo "       mark K8 has left to pull down; the bare-metal runtime names no OS"
        echo "       call at all; and the probe ran, with its arena reserved, its lock"
        echo "       held and its sum exact."
        abschnitt_fertig
        exit 0
    fi
    # The red of a COMPLETE run: every stage above has spoken, so this is a
    # finding and not a cut -- and it says which, instead of leaving the reader
    # to guess from a `1`.
    abschnitt_fertig
    echo "RED: $n finding(s)."
    exit 1
fi

if [ "$GIFT" = all ]; then
    LISTE="$(gifte)"
else
    LISTE="$GIFT"
fi
stufe_still "die Giftlaeufe"
gefangen=0
gesamt=0
for g in $LISTE; do
    gesamt=$((gesamt+1))
    arb="$ARB/g$g"
    mkdir -p "$arb"
    einmal "$arb" "$g" > "$arb/aus.txt"
    ergebnis="$(beurteile "$arb/aus.txt" "$g")"
    n="$(echo "$ergebnis" | sed -n 's/^FEHLER=//p')"
    # **A gift that did not APPLY is not a gift that was caught** -- the trap
    # this lane has paid for three times (`~/claude-lane/STAND.md`). A mutation
    # whose target has moved leaves a run that measures nothing, and its red (or
    # its green) says nothing either way.
    if grep -qE "does not apply|does not measure" "$arb/aus.txt"; then
        echo "GIFT $g: DOES NOT APPLY -- the mutation measured nothing, so its verdict says nothing"
        grep -E "does not apply|does not measure" "$arb/aus.txt" | head -1 | sed 's/^/    /'
    elif [ "$n" = 0 ]; then
        echo "GIFT $g: NOT CAUGHT -- the harness stayed green under the mutation"
    else
        echo "GIFT $g: caught ($n finding(s))"
        echo "$ergebnis" | grep -E '^RED|^     |^       ' | head -10 | sed 's/^/    /'
        gefangen=$((gefangen+1))
    fi
done
echo
echo "gifts: $gefangen of $gesamt caught"
abschnitt_fertig
[ "$gefangen" = "$gesamt" ]
