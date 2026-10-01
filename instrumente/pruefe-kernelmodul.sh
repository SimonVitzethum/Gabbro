#!/usr/bin/env bash
# instrumente/pruefe-kernelmodul.sh -- a Gabbro unit AS A LINUX KERNEL MODULE,
# built and LOADED, in QEMU only (server lane, TODO section 0e K4/K5).
#
# THE QUESTION: does a Gabbro program with a bounded heap become a Linux kernel
# module that loads, allocates, hits refuse-on-full where the program says so,
# reports it, and unloads with no oops and no warning?
#
# IN QEMU ONLY, and that is a hard rule of this machine (`~/claude-lane/REGELN.md`):
# nothing built here is ever `insmod`ed into the host kernel. The harness boots
# a copy of this host's kernel (`~/claude-lane/vm/vmlinuz`, 6.8.0-139-generic)
# with a busybox initramfs, loads the module there, reads `dmesg`, unloads, and
# powers the machine off.
#
# THE RECIPE:
#   1. `gabbro emit` the unit;
#   2. build the module against the host's kernel headers (`gabbro build`): the
#      emitted C, the program's OWN foreign bodies and its binding, and the
#      module driver the build WRITES (C-free lane, C2: the loader's two entry
#      points, the arena pools of the manifest's PROVISION -- smaller than the
#      program's declared ceiling for `halde` -- the lock primitives over the
#      binding, one thread per root; no handwritten runtime file);
#   3. boot QEMU, `insmod`, `rmmod`, and hold the kernel log against the
#      expected lines.
#
# WHAT MAKES A GREEN RUN A MEASUREMENT -- the Sprechprobe (speech test) of this
# instrument:
# `--gift N` mutates the harness and the run must turn RED. The mutations are listed in `gifte()` below; `--gift all`
# runs every one of them and reports how many were caught.
#
# Missing `qemu-system-x86_64`, `busybox`, `cpio`, the kernel headers or the VM
# kernel prints `KERNELMODUL: NOT RUN` with the reason -- never a pass line.
#
# Usage: instrumente/pruefe-kernelmodul.sh [--gift N|all] [--keep]
set -u

W="$(cd "$(dirname "$0")/.." && pwd)"
GIFT=""
KEEP=0
while [ $# -gt 0 ]; do
    case "$1" in
        --gift) shift; GIFT="$1" ;;
        --keep) KEEP=1 ;;
        *) echo "pruefe-kernelmodul.sh: unknown argument '$1'" >&2; exit 2 ;;
    esac
    shift
done

# -- the two probes, and what each expects, in one place ----------------------
#
# THREE PROBES, because the module target answers three questions and one
# program cannot ask them all. `halde` is the bounded heap (acceptance point 3);
# `takt` is `masks irqs` (K3); `atomar` is a Gabbro `atomic` lowered onto the
# kernel's own memory model (K6, acceptance point 4b). They share everything
# below this block -- one build recipe, one initramfs shape, one verdict
# function.
#
# `halde` -- `messung/proben/kmodul/halde-treiber.gab` declares `arena Knoten
# capacity 2 .. 4 max 4096 of Wert` (8-byte slots) and grows it three times by
# 1024. The whole-run upper bound is 4 + 3072 = 3076 slots, below the ceiling,
# so `N426` admits all three. The PROVISION is 24 KiB = 3072 slots' worth minus
# a little: two grows fit (4 + 2048 = 2052 slots = 16416 bytes), the third does
# not (3076 slots = 24608 bytes > 24576). So the third `grow` is refused BELOW
# the ceiling and the program's `else` runs -- refuse-on-full, deliberately
# reached, not hoped for.
#
# `takt` -- `messung/proben/kmodul/sperre-takt.gab` holds a `masks irqs` lock
# across a 4096-slot traversal, 64 times over, while the program's own C runs a
# 50 us hardirq timer whose body takes the same lock, all on ONE core. A run that
# FINISHES says no interrupt ever arrived inside a section (one that did would
# wait for the core it interrupted -- gift 5); `ticks` says the timer fired at
# all, WITHOUT WHICH a finished run measures nothing. Both are checked.
#
# `atomar` -- `messung/proben/kmodul/atomar-faeden.gab` declares TWO CONCURRENT
# ROOTS and four atomics. `gabbro build` writes the roots into the module driver,
# which starts one kernel thread per root through the binding, joining both before the
# unload function reports. The four numbers the run must show are exact and each
# one is a different row of the mapping: a saturating counter bumped 256 times
# by each root (the bounded CAS loop, answer 512), how often the release/acquire
# flag was seen set (> 0, or the run measured nothing), how often it was seen
# set over a payload that was still 0 (must be 0), and a bit word each root ORs
# its own bit into (one `atomic_fetch_or_explicit`, answer 3). Since the C-free
# lane's C2 every form is the compiler's C11 builtin (the generated
# `<stdatomic.h>`), not a kernel macro.
#
# **A green run of this probe does not measure the BARRIERS**, and the file says
# so: on x86 acquire and release are free, so no run here could tell a correct
# mapping from one that dropped them. That is what the mapping stage below is
# for -- it expands every (form, ordering) pair and holds it against the
# builtin and the ordering the row requires, and gift 8 drops an ordering.
#
# **The arenas, the locks and the roots are NOT named here.** The emitted unit
# carries its own arena list (`#define GABBRO_ARENEN`, emitter) and `gabbro build`
# writes the locks and the roots into the module driver (out of the same walk the
# hosted and the bare-metal driver read) -- a harness that
# repeated any of them would be a second register over one fact, and the one
# nobody reads is the one that drifts (`W7`).
PROBEN="halde takt atomar"

probe_waehle() {   # $1 = probe name; sets QUELLE FREMD MODUL INIT EXIT VORRAT ERWARTET FRIST
    # **Every per-probe variable is cleared first.** Without this line `TICKS_MIN`
    # survived from one probe into the next and `halde` -- which has no timer --
    # was RED for a tick count it never claimed to have. *A selector that only
    # ever sets is a selector that carries the last probe's answer.*
    unset TICKS_MIN GESEHEN_MIN ABBILDUNG
    QUELLE=""; FREMD=""; MODUL=""; INIT=""; EXIT=""; VORRAT=""; ERWARTET=""; FRIST=600
    # **The BINDING, as manifest file lines** (K7, session 6). Every kernel function the
    # module driver calls is declared by the program and defined in the program's own C;
    # `bibliothek/linux-kmod` is the binding a program takes off the shelf, and these are
    # the lines that name it.
    BINDUNG="$W/bibliothek/linux-kmod/linux-kmod.gab"
    # What the RUNTIME still takes from the kernel, per probe. **0 since K7 landed**
    # (session 6), and it is a wall now and no longer a ratchet: the twelve names of the
    # worklist are the program's, so a single one back in the runtime is a finding.
    MARKE_KSYM=0
    # One vCPU unless the probe needs two; TCG is slow and a second core costs
    # boot time that only the concurrent probe has a use for.
    SMP=1
    case "$1" in
        halde)
            QUELLE="$W/messung/proben/kmodul/halde-treiber.gab"
            # No C of its own since the C-free lane's C2: the report is Gabbro over the
            # binding's `gabbro_kern_zeige`.
            MODUL=gabbro_halde
            INIT=laden
            EXIT=entladen
            # The PROVISION is the manifest's word since the C-free lane's C2 (a static
            # pool per arena in the generated driver; no `module_param` any more).
            VORRAT=24576
            # The kernel lines the run must show, in this order. `k=2 v=33` is
            # the read-back (11 + 22 through the arena), `k=3 v=3` is the THIRD
            # grow refusing.
            ERWARTET="gabbro-halde: k=1 v=0
gabbro-halde: k=2 v=33
gabbro-halde: k=3 v=3
gabbro-halde: k=9 v=0"
            ;;
        takt)
            QUELLE="$W/messung/proben/kmodul/sperre-takt.gab"
            FREMD="$W/messung/proben/kmodul/takt.c"
            MODUL=gabbro_takt
            INIT=laden
            EXIT=entladen
            # A run of this probe finishes in about five seconds; the poison run
            # that takes the lock UNMASKED does not finish at all (the timer body
            # waits for the core it interrupted). 45 s is far past the first and
            # far short of an hour.
            FRIST=45
            ERWARTET="gabbro-takt: k=1 v=0
gabbro-takt: ticks=
gabbro-takt: k=9 v=0"
            # A run whose timer never fired finishes too and has measured
            # nothing (`W1`): the verdict below demands this many ticks.
            TICKS_MIN=5
            ;;
        atomar)
            QUELLE="$W/messung/proben/kmodul/atomar-faeden.gab"
            # No C of its own since the C-free lane's C2 (report and stop over the binding).
            MODUL=gabbro_atomar
            INIT=laden
            EXIT=entladen
            # Two vCPUs, so the two declared roots really run at the same time.
            # With one, a lost update in the CAS loop would need a preemption to
            # show at all -- the answer would be 512 either way and the run would
            # measure the counter's arithmetic, not its atomicity.
            SMP=2
            FRIST=120
            # The four numbers, exact, in the order the unload function writes
            # them. `k=2 v=512` is the counter (256 rounds x 2 roots), `k=4 v=0`
            # the payload check, `k=5 v=3` the two bits.
            ERWARTET="gabbro-atomar: k=1 v=0
gabbro-atomar: k=2 v=512
gabbro-atomar: k=4 v=0
gabbro-atomar: k=5 v=3
gabbro-atomar: k=9 v=0"
            # `k=3` is NOT in the list above, because it is not a constant: how
            # often the consumer saw the flag set depends on the scheduling. A
            # run in which it was never seen reports a clean `k=4 v=0` and has
            # measured NOTHING about the flag (`W1`), so the verdict demands a
            # minimum instead of a value -- the same shape `takt` gives `ticks`.
            GESEHEN_MIN=1
            # And the mapping itself is checked where the module was BUILT: the
            # rows are expanded and held against the primitives they require.
            ABBILDUNG=1
            # The memory model of an `atomic` is the COMPILER's C11 builtins since the C-free
            # lane's C2: `gabbro build` writes `inc/stdatomic.h` (`treiber::KMOD_STDATOMIC`),
            # which is what the mapping stage below reads. No binding line for it.
            ;;
        *) echo "pruefe-kernelmodul.sh: no such probe '$1'" >&2; exit 2 ;;
    esac
}

# -- the mapping, measured by EXPANDING it (server lane, TODO section 0e K6; the
#    builtin mapping since the C-free lane's C2) ---------------------------------
#
# THE PROBLEM THIS SOLVES. `atomic` in a kernel module is lowered by the generated
# `inc/stdatomic.h`: each of the emitter's nine C11 call forms onto the compiler's
# `__atomic` builtin of the same operation, the ORDERING passed through. A header
# that quietly dropped an ordering -- acquire lowered as relaxed -- would compile,
# load, run and answer every expected number, BECAUSE THIS IS x86: acquire and
# release are free there, and the barriers a weak-memory architecture is owed
# leave no trace in a green run on this machine. *A measurement that cannot fail
# is not a measurement* (`W1`).
#
# So the mapping is measured where it can fail: in the PREPROCESSOR. Each row is
# expanded on its own line and held against the builtin it must use AND the
# ordering(s) it must hand over. The expansion is of the header IN THE BUILD
# DIRECTORY -- the copy the `.ko` was actually built from -- so this is a reading
# of the artefact and not of the tree, and gift 8 (an ordering dropped) is
# caught here.
#
# The table below is a SPECIFICATION and the header is its implementation, so
# the two are not a second register over one fact: this is the shape of a poison
# probe, not of a duplicated list.
abbildung_pruefe() {   # $1 = the module build dir (its `inc/` holds stdatomic.h)
    local kdir="$1" arb="$1/abbildung" befunde=0 zeile marke muss text
    rm -rf "$arb"; mkdir -p "$arb"
    cat > "$arb/rows.c" <<'EOF'
#include <stdatomic.h>
_Atomic unsigned int A;
void f(void) {
Z01 atomic_load_explicit(&A, memory_order_relaxed);
Z02 atomic_load_explicit(&A, memory_order_acquire);
Z03 atomic_load_explicit(&A, memory_order_seq_cst);
Z04 atomic_store_explicit(&A, 1u, memory_order_relaxed);
Z05 atomic_store_explicit(&A, 1u, memory_order_release);
Z06 atomic_store_explicit(&A, 1u, memory_order_seq_cst);
Z07 atomic_fetch_add_explicit(&A, 1u, memory_order_relaxed);
Z08 atomic_fetch_add_explicit(&A, 1u, memory_order_acq_rel);
Z09 atomic_fetch_add_explicit(&A, 1u, memory_order_seq_cst);
Z10 atomic_fetch_or_explicit(&A, 1u, memory_order_relaxed);
Z11 atomic_compare_exchange_weak_explicit(&A, &A, 1u, memory_order_relaxed, memory_order_relaxed);
Z12 atomic_compare_exchange_strong_explicit(&A, &A, 1u, memory_order_release, memory_order_acquire);
Z13 atomic_compare_exchange_weak_explicit(&A, &A, 1u, memory_order_seq_cst, memory_order_seq_cst);
Z14 atomic_fetch_sub_explicit(&A, 1u, memory_order_release);
Z15 atomic_fetch_and_explicit(&A, 1u, memory_order_acquire);
Z16 atomic_fetch_xor_explicit(&A, 1u, memory_order_seq_cst);
}
EOF
    if ! cc -E -P -nostdinc -I "$kdir/inc" "$arb/rows.c" \
            > "$arb/rows.i" 2> "$arb/rows.err"; then
        echo "HARNESS: mapping FAILED -- the header did not preprocess"
        sed 's/^/    /' "$arb/rows.err" | head -5
        return 0
    fi
    # And the header must COMPILE with the kernel's own compiler over the rows (a builtin
    # the compiler cannot inline would be a call to a library the kernel does not have).
    sed 's/^Z[0-9]* //' "$arb/rows.c" > "$arb/rows-cc.c"
    if ! cc -c -std=gnu11 -O2 -nostdinc -I "$kdir/inc" "$arb/rows-cc.c" -o "$arb/rows.o" \
            2> "$arb/rows-cc.err"; then
        echo "HARNESS: mapping FAILED -- the rows did not compile"
        sed 's/^/    /' "$arb/rows-cc.err" | head -5
        return 0
    fi
    if nm -u "$arb/rows.o" | grep -q .; then
        echo "HARNESS: mapping FAILED -- the rows call a library: $(nm -u "$arb/rows.o" | awk '{print $2}' | tr '\n' ' ')"
        return 0
    fi
    # marker | what the row MUST expand to (builtin and ordering) | the row in words
    while IFS='|' read -r marke muss was; do
        [ -z "$marke" ] && continue
        # One source line expands to one output line -- a macro expansion never
        # introduces a newline -- so a row is exactly the line its marker opens.
        text="$(grep -m1 "^$marke" "$arb/rows.i")"
        if [ -z "$text" ]; then
            echo "HARNESS: mapping FAILED -- the row $was ($marke) did not survive preprocessing"
            befunde=$((befunde+1))
            continue
        fi
        if ! printf '%s' "$text" | grep -qE "$muss"; then
            echo "HARNESS: mapping FAILED -- $was does not expand to $muss"
            befunde=$((befunde+1))
        fi
    done <<'EOF'
Z01|__atomic_load *\([^;]*\(memory_order_relaxed\)\)|load relaxed
Z02|__atomic_load *\([^;]*\(memory_order_acquire\)\)|load acquire
Z03|__atomic_load *\([^;]*\(memory_order_seq_cst\)\)|load seq_cst
Z04|__atomic_store *\([^;]*\(memory_order_relaxed\)\)|store relaxed
Z05|__atomic_store *\([^;]*\(memory_order_release\)\)|store release
Z06|__atomic_store *\([^;]*\(memory_order_seq_cst\)\)|store seq_cst
Z07|__atomic_fetch_add *\(.*\(memory_order_relaxed\)\)|fetch_add relaxed
Z08|__atomic_fetch_add *\(.*\(memory_order_acq_rel\)\)|fetch_add acq_rel
Z09|__atomic_fetch_add *\(.*\(memory_order_seq_cst\)\)|fetch_add seq_cst
Z10|__atomic_fetch_or *\(.*\(memory_order_relaxed\)\)|fetch_or relaxed
Z11|__atomic_compare_exchange *\(.*, *1, *\(memory_order_relaxed\), *\(memory_order_relaxed\)\)|compare-exchange weak (relaxed, relaxed)
Z12|__atomic_compare_exchange *\(.*, *0, *\(memory_order_release\), *\(memory_order_acquire\)\)|compare-exchange strong (release, acquire)
Z13|__atomic_compare_exchange *\(.*, *1, *\(memory_order_seq_cst\), *\(memory_order_seq_cst\)\)|compare-exchange weak (seq_cst, seq_cst)
Z14|__atomic_fetch_sub *\(.*\(memory_order_release\)\)|fetch_sub release
Z15|__atomic_fetch_and *\(.*\(memory_order_acquire\)\)|fetch_and acquire
Z16|__atomic_fetch_xor *\(.*\(memory_order_seq_cst\)\)|fetch_xor seq_cst
EOF
    # And the enumeration the orderings stand for: each C11 name IS the compiler's constant.
    for o in RELAXED ACQUIRE RELEASE ACQ_REL SEQ_CST; do
        local klein; klein="$(printf '%s' "$o" | tr 'A-Z' 'a-z')"
        grep -q "memory_order_$klein = __ATOMIC_$o" "$kdir/inc/stdatomic.h" || {
            echo "HARNESS: mapping FAILED -- memory_order_$klein is not __ATOMIC_$o"
            befunde=$((befunde+1))
        }
    done
    if [ "$befunde" = 0 ]; then
        echo "HARNESS: mapping ok (16 rows expanded and held against their builtin and ordering)"
    fi
}

# -- which kernel functions does the RUNTIME call? (server lane, TODO 0e K7) ---
#
# SIMON'S RULE: *"API calls are always user-made"* -- a Gabbro kernel module
# reaches the kernel only through items the PROGRAM declares. It held for
# everything the program wrote: `messung/proben/kmodul/atomar.c` calls `pr_info`
# and `panic` because `atomar-faeden.gab` declared those two foreign functions
# with their ABI, their effects, their costs and the assumption their bodies
# keep. **Until 2026-09-28 it did NOT hold for the runtime beside it:**
# `laufzeit/kmodul/kmodul.c` called `kthread_run` and `wait_for_completion`,
# `arena.c` called `vzalloc` and `vfree`, `sperre.h` expanded to
# `raw_spin_lock_irqsave`, and none of those names came from a program.
# `AUFTRAG-1.md` K7 (Simon, 2026-09-28) said they were to.
#
# THIS STAGE IS THE MEASUREMENT THAT MADE THAT A NUMBER, and the number is 0
# since K7 landed. Per probe:
#
#   * `nm -u <unit>.ko` -- every kernel symbol the whole module still needs;
#   * `nm -u` over the RUNTIME objects only (`gabbro_kmodul.o`, which is where
#     the emitted unit is #included too, and `gabbro_arena.o`);
#   * the INTERSECTION is what the runtime pulls out of the kernel. A symbol the
#     program's own C pulls (`panic` from `aufgegeben`) is not in it, because
#     that reference lives in `gabbro_fremd*.o`.
#
# Minus the toolchain's own names (`__fentry__`, the return thunk, UBSan's
# handlers, the stack guard): those are not API calls and no program could
# declare them.
#
# **A WALL SINCE K7 LANDED, and a ratchet before it.** Session 5 measured the
# number and could not demand 0: the runtime hard-wired twelve names, and a stage
# that was red on every probe until the work landed is a red nobody reads. So the
# mark was the measured number and the stage refused only a run that needed MORE.
#
#   halde   4  param_ops_uint, _printk, vfree, vzalloc
#   takt    7  + pcpu_hot, _raw_spin_lock_irqsave, _raw_spin_unlock_irqrestore
#   atomar  9  + complete, __init_swait_queue_head, kthread_create_on_node,
#                wait_for_completion, wake_up_process (and no lock)
#
# **Session 6 brought all twelve into the program** (`laufzeit/kmodul/bindung.h`
# declares what the runtime calls, `bibliothek/linux-kmod/` defines it), and the
# mark is 0 on every probe. The `.ko` still IMPORTS those twelve -- it must, the
# program calls them -- but the reference lives in the object the PROGRAM
# supplied, which is exactly what the per-object criterion below was built to
# tell apart. *The stage measures the fix and not a proxy for it, which is why it
# could be written before the fix existed.*
#
# The direction that stays a finding is the other one: a run that needs FEWER
# than the mark is reported too (the good case, the mark is stale and belongs
# pulled down), in the shape `pruefe-emission.sh` uses for its emission counters.
# At a mark of 0 only one direction is left, and that makes this a wall.
KSYM_TOOLKETTE='^(__fentry__|__x86_return_thunk|__stack_chk_|__ubsan_handle_|__sanitizer_)'

symbole_pruefe() {   # $1 = module build dir, $2 = module name, $3 = the mark
    local kdir="$1" modul="$2" marke="$3" arb="$1/ksym" n
    mkdir -p "$arb"
    nm -u "$kdir/$modul.ko" 2>/dev/null | awk '{print $2}' | sort -u > "$arb/ko.txt"
    # **What the DRIVER TEXT names** (C-free lane, C2): the generated `gabbro_kmodul.c`
    # includes the emitted unit, whose binding is Gabbro since slice 2 and calls the kernel
    # by its own `extern fn` declarations -- the program's calls, compiled into the same
    # object. So the runtime's share is the kernel symbols the driver's OWN text names: every
    # identifier of `gabbro_kmodul.c` (the include line and comments removed) that the `.ko`
    # imports. Gift 11 plants one there.
    sed -e 's|/\*.*\*/||g' -e '/^#include/d' "$kdir/gabbro_kmodul.c" \
        | grep -oE '[A-Za-z_][A-Za-z0-9_]*' | sort -u > "$arb/rt.txt"
    comm -12 "$arb/ko.txt" "$arb/rt.txt" | grep -Ev "$KSYM_TOOLKETTE" > "$arb/fest.txt"
    n="$(wc -l < "$arb/fest.txt" | tr -d ' ')"
    if [ "$n" -gt "$marke" ]; then
        echo "HARNESS: kernel symbols FAILED -- the runtime hard-wires $n kernel function(s), the mark is $marke"
        sed 's/^/    hard-wired: /' "$arb/fest.txt" | head -20
        return 0
    fi
    if [ "$n" -lt "$marke" ]; then
        echo "HARNESS: kernel symbols FAILED -- the runtime hard-wires $n, below the mark of $marke: the mark belongs pulled down (the good case, and a finding nonetheless)"
        return 0
    fi
    echo "HARNESS: kernel symbols ok ($n hard-wired by the runtime, mark $marke)"
}

KERNVERSION="$(uname -r)"
KBUILD="/lib/modules/$KERNVERSION/build"
VMLINUZ="${GABBRO_VMLINUZ:-$HOME/claude-lane/vm/vmlinuz}"

nicht_gelaufen() {
    echo "KERNELMODUL: NOT RUN -- $1"
    exit 2
}

for werkzeug in qemu-system-x86_64 busybox cpio make gzip; do
    command -v "$werkzeug" >/dev/null 2>&1 || nicht_gelaufen "no $werkzeug on this machine"
done
[ -d "$KBUILD" ]  || nicht_gelaufen "no kernel headers at $KBUILD"
[ -r "$VMLINUZ" ] || nicht_gelaufen "no VM kernel at $VMLINUZ (set GABBRO_VMLINUZ)"
for p in $PROBEN; do
    probe_waehle "$p"
    [ -f "$QUELLE" ] || nicht_gelaufen "no probe source at $QUELLE"
    [ -z "$FREMD" ] || [ -f "$FREMD" ] || nicht_gelaufen "no probe C body at $FREMD"
done

# **Which binary, and is it newer than the sources?** One register, one file:
# `instrumente/binaer.sh` -- and this instrument is one of the three the trap bit.
. "$(dirname "$0")/binaer.sh"
GABBRO="$(gabbro_binaer "$W")" || nicht_gelaufen "$GABBRO"

# -- the mutations (`--gift`) --------------------------------------------------
#
# Each one is a change to the HARNESS or to what it feeds the kernel, and each
# one must turn the run red. They are chosen so that no two are caught by the
# same check:
#
#   1 the expected read-back value moves (33 -> 34): does the run really read
#     the kernel log, or does it only look at insmod's exit code?
#   2 the manifest's provision is raised past the third grow (24 -> 64 KiB): the refusal
#     line `k=3 v=3` must then be MISSING -- does the run notice a line that
#     did not come, or only lines that did?
#   3 the module's unload line is dropped from the expectation's check by
#     rmmod'ing nothing: does the run see an unload that did not happen?
#   4 the emitted C is replaced by one whose arena ceiling is 4 (below the
#     grows the program makes): every `grow` is then past `max`, which is a
#     fail-stop and not a branch, and the load must refuse.
#     *This gift found something.* The first time it ran, `insmod` SUCCEEDED:
#     the runtime set its load error and returned false, the program's `else`
#     ran, the unit answered 0, and `module_init` -- which read the load error
#     only BEFORE calling the unit -- let the module in. A fail-stop that does
#     not reach the loader is not a fail-stop. The load function (now the generated
#     driver, template `modul.lebenslauf`) reads it again after the unit's init, and the gift is caught at
#     `insmod` as well as in the log.
#
# The `takt` probe's three (K3, and 5 is the one that is about the LOWERING and
# not about the harness):
#
#   5 the generated driver's masked `TAKT` pair is edited into the plain one and
#     the module re-made with the `Kbuild` the build wrote:
#     the lock then takes `raw_spin_lock` instead of `raw_spin_lock_irqsave`, the
#     hardirq timer body lands inside a critical section on the core that holds
#     it, and waits for that core. *The run does not finish* -- exactly what the
#     bare-metal harness sees for the same mutation (`pruefe-metall.sh`, image
#     `metall59-gift`). This is the poison probe of the masking itself: without
#     it, GREEN would only say that nothing bad happened to be observed.
#   6 the timer period is raised past the whole run (50 us -> 50 s) in the
#     program's own C: the timer then never fires, `ticks=0`, and the run must be
#     RED because it measured NOTHING -- a finished run over zero
#     opportunities is not a measurement (`W1`).
#   7 the expected `k=9 v=0` (the unload's line) moves to `k=9 v=1`: does the run
#     read the kernel log, or only the exit codes? (The `halde` twin of this is
#     gift 1.) Until 2026-10-01 it moved `landed=0`, a count the probe no longer
#     prints (C2 slice 3: on one core it could only be 0 in a run that finished).
#
# The `atomar` probe's three (K6, and 8 is the one that is about the LOWERING
# and not about the harness):
#
#   8 the ATOMIC MAPPING is made deliberately too weak in the copy the module
#     was built from (`inc/stdatomic.h`): the load and the store drop the
#     ordering they are handed for relaxed. **On x86 the run would still answer every
#     expected number** -- acquire and release are free there -- so a harness
#     that only booted the module would call this green, and the barriers a
#     weak-memory architecture is owed would be gone in silence. It is caught by
#     the mapping stage, which expands the rows and holds each against the
#     primitive it must select. *This gift is the reason that stage exists.*
#   9 a PLAIN ACCESS replaces one of the calls in the emitted C
#     (`atomic_load_explicit(&NUTZLAST, …)` becomes `NUTZLAST`). On a C11
#     `_Atomic` object that would still be an atomic operation; in the module
#     target `_Atomic` is `volatile`, so it is an unordered access that compiles
#     without a word. Caught by `instrumente/pruefe-atomar-zugriffe.py` over the
#     emitted C in the build directory.
#  10 the expected counter moves (512 -> 513): does the run read the kernel log?
#     (The `halde` twin is gift 1, the `takt` twin gift 7.)
#
# And the two poison probes of K7, one per half:
#
#  11 the RUNTIME gains one kernel call it did not have (`msleep` in
#     `gabbro_kmodul.c`, in the build directory, re-made with the `Kbuild` the
#     build wrote). The hard-wired count then stands at 1 against a mark of 0 and
#     the run must be RED. *Without this gift the kernel-symbol stage would only
#     say that nothing happened to be noticed* -- and it is the stage that says
#     the runtime calls no kernel function, so it is the one that must be known
#     to bite.
#  12 the PROGRAM loses its binding: the two `bibliothek/linux-kmod` lines are
#     dropped from the manifest and nothing else changes. `gabbro build` must
#     refuse the unit before a byte of C is written, with the binding rule's own
#     sentence (`bau.rs::bindungsregel`), and the harness checks for THAT
#     sentence -- a build that refused for another reason, or one that accepted
#     and then died at `modpost` over a name the program never wrote, is reported
#     as measuring nothing. *This is the half gift 11 cannot reach: a unit whose
#     binding is missing has no `.ko` for the symbol stage to read.*
gifte() { echo "1 2 3 4 5 6 7 8 9 10 11 12"; }

# Which probe a gift belongs to -- a gift is a mutation OF a run, and a run is
# of one probe.
gift_probe() {
    case "$1" in
        1|2|3|4)  echo halde ;;
        5|6|7)    echo takt ;;
        8|9|10)   echo atomar ;;
        11)       echo halde ;;
        # Gift 12 runs on `takt` since the C-free lane's C2: `halde` and `atomar` report
        # through the binding's Gabbro functions by name (`use linux::kmod::…`), so without
        # the binding they fall at name resolution before the binding rule could speak.
        12)       echo takt ;;
        *) echo "pruefe-kernelmodul.sh: no such gift '$1'" >&2; exit 2 ;;
    esac
}

lauf_einmal() {   # $1 = gift number or "", $2 = work dir, $3 = probe
    local gift="$1"
    local arb="$2"
    probe_waehle "$3"
    local rmmod_zeile="/bin/busybox rmmod $MODUL && echo \"HARNESS: rmmod ok\" || echo \"HARNESS: rmmod FAILED\""

    # **The module is built by `gabbro build`, not by this harness** (server lane,
    # 2026-09-28). Until today the Kbuild, the runtime copies and the `-D`s stood HERE, in
    # shell, and `gabbro build` could not make a kernel module at all -- two registers over
    # one artefact, and the one in the shell is the one a user never gets (`W7`). The
    # manifest below is the whole of what this harness now knows about building: two paths
    # and the two calls the kernel makes.
    mkdir -p "$arb"
    # **Gift 12 takes the BINDING away**, and nothing else: the unit still declares its
    # arena, its lock or its roots, and the module runtime still calls the binding names of
    # the generated module driver. `gabbro build` must refuse it BEFORE a byte of C is
    # written -- which is the half of K7 no measurement over a built `.ko` could give,
    # because a unit whose binding is missing has no `.ko` to measure.
    local bindung="$BINDUNG"
    [ "$gift" = 12 ] && bindung=""
    {
        echo "-- written by instrumente/pruefe-kernelmodul.sh"
        echo "compiler cc -std=c11 -Wall -Wextra -Werror"
        echo "out $arb/bau"
        # The loader's two entry symbols and the licence are the MANIFEST's words (C-free
        # lane, C2): the build writes the module runtime and names no kernel symbol itself.
        echo "kmod $KBUILD init_module cleanup_module"
        echo "note .modinfo license=Dual MIT/GPL"
        echo "note .modinfo description=a Gabbro unit as a Linux kernel module"
        local vorrat="$VORRAT"
        [ "$gift" = 2 ] && vorrat=65536
        [ -n "$vorrat" ] && echo "provision $vorrat"
        echo "unit $MODUL module $INIT $EXIT"
        echo "  $QUELLE"
        [ -n "$FREMD" ] && echo "  $FREMD"
        printf '%s\n' "$bindung" | while IFS= read -r f; do
            [ -n "$f" ] && echo "  $f"
        done
    } > "$arb/manifest"
    if ! "$GABBRO" build "$arb/manifest" > "$arb/bau.log" 2>&1; then
        echo "HARNESS: gabbro build FAILED"
        if [ "$gift" = 12 ] && ! grep -q 'binds no `gabbro_kern_' "$arb/bau.log"; then
            # *A gift that turned the run red for the wrong reason has measured nothing*
            # -- the same reading `DOES NOT APPLY` already has for a mutation that found
            # nothing to change (session 5, gift 8).
            echo "HARNESS: gift 12 does not measure -- the build refused, and not with the binding rule"
        fi
        tail -25 "$arb/bau.log" >&2
        return 0
    fi
    if [ "$gift" = 12 ]; then
        echo "HARNESS: gift 12 does not measure -- the build ACCEPTED a module with no binding, so the red below is some other door's"
    fi
    if [ "$gift" = 4 ]; then
        # **A ceiling of 4 slots: every `grow` is past it**, so the runtime fail-stops and
        # `module_init` must refuse the load. The mutation is on the EMITTED C inside the
        # build directory `gabbro build` left behind, and the module is re-made with the
        # `Kbuild` the build wrote -- so this gift carries no second copy of the recipe
        # either. (Mutating the SOURCE would be refused by `N426` one door earlier, and
        # then the fail-stop never runs.)
        local kdir="$arb/bau/$MODUL.kmod"
        sed -i 's/(uint32_t)(4096)/(uint32_t)(4)/' "$kdir/einheit.c"
        sed -i 's/_Static_assert((4) <= (4096)/_Static_assert((4) <= (4)/' "$kdir/einheit.c"
        rm -f "$kdir/$MODUL.ko" "$kdir"/*.o
        if ! make -C "$KBUILD" "M=$(cd "$kdir" && pwd)" modules > "$arb/make.log" 2>&1; then
            echo "HARNESS: the mutated module did not build"
            tail -20 "$arb/make.log" >&2
            return 0
        fi
        cp "$kdir/$MODUL.ko" "$arb/bau/$MODUL.ko"
    fi
    if [ "$gift" = 5 ] || [ "$gift" = 6 ]; then
        # **The two `takt` mutations that need a re-make**, both on what the build
        # left behind, so neither carries a second copy of the recipe:
        #   5 the lock loses its mask in the unit's OWN list -- the lowering poison;
        #   6 the timer period is raised past the run in the program's OWN C, so the
        #     timer never fires and the run measures nothing.
        local kdir="$arb/bau/$MODUL.kmod"
        if [ "$gift" = 5 ]; then
            # The lock primitives are GENERATED text of the driver (`gabbro_kmodul.c`,
            # written by `gabbro build`, C-free lane C2). *They stood in a generated
            # `sperren.h` before, and in `einheit.c` for one afternoon before that; each move
            # made this mutation stop applying, and a gift that does not apply looks exactly
            # like a pass -- so it says so itself.* The masked pair becomes the plain one.
            local kd="$kdir/gabbro_kmodul.c"
            grep -q 'uint64_t f = gabbro_kern_sperre_nimm_maskiert(gabbro_sperre_TAKT);' "$kd" \
                && grep -q 'gabbro_kern_sperre_gib_maskiert(gabbro_sperre_TAKT, f);' "$kd" || {
                echo "HARNESS: gift 5 does not apply -- no masked TAKT pair in gabbro_kmodul.c"
                return 0
            }
            sed -i 's/uint64_t f = gabbro_kern_sperre_nimm_maskiert(gabbro_sperre_TAKT);/uint64_t f = 0; gabbro_kern_sperre_nimm(gabbro_sperre_TAKT);/' "$kd"
            sed -i 's/gabbro_kern_sperre_gib_maskiert(gabbro_sperre_TAKT, f);/(void)f; gabbro_kern_sperre_gib(gabbro_sperre_TAKT);/' "$kd"
        else
            sed -i 's/GABBRO_TAKT_NS 50000ull/GABBRO_TAKT_NS 50000000000ull/' "$kdir/gabbro_fremd0.c"
        fi
        rm -f "$kdir/$MODUL.ko" "$kdir"/*.o
        if ! make -C "$KBUILD" "M=$(cd "$kdir" && pwd)" modules > "$arb/make.log" 2>&1; then
            echo "HARNESS: the mutated module did not build"
            tail -20 "$arb/make.log" >&2
            return 0
        fi
        cp "$kdir/$MODUL.ko" "$arb/bau/$MODUL.ko"
    fi
    if [ "$gift" = 8 ] || [ "$gift" = 9 ]; then
        # **The two `atomar` mutations that need a re-make**, both on what the build
        # left behind, so neither carries a second copy of the recipe:
        #   8 the mapping is made too weak in the copy the module is built from;
        #   9 a plain access replaces one of the nine calls in the emitted C.
        local kdir="$arb/bau/$MODUL.kmod"
        if [ "$gift" = 8 ]; then
            # **The two rows are matched WHOLE and by fixed string**, before and after:
            # the load and the store DROP the ordering they are handed and use relaxed.
            # On x86 the run still answers every number; the mapping stage must say no.
            local zeile_a='__atomic_load(__gabbro_p, &__gabbro_w, (O));'
            local zeile_r='__atomic_store(__gabbro_p, &__gabbro_w, (O));'
            local h="$kdir/inc/stdatomic.h"
            grep -Fq "$zeile_a" "$h" && grep -Fq "$zeile_r" "$h" || {
                echo "HARNESS: gift 8 does not apply -- the load/store rows are not where it looks"
                return 0
            }
            sed -i 's/__atomic_load(__gabbro_p, &__gabbro_w, (O));/__atomic_load(__gabbro_p, \&__gabbro_w, __ATOMIC_RELAXED);/' "$h"
            sed -i 's/__atomic_store(__gabbro_p, &__gabbro_w, (O));/__atomic_store(__gabbro_p, \&__gabbro_w, __ATOMIC_RELAXED);/' "$h"
            if grep -Fq "$zeile_a" "$h" || grep -Fq "$zeile_r" "$h"; then
                echo "HARNESS: gift 8 does not apply -- a row did not change"
                return 0
            fi
        else
            grep -q 'atomic_load_explicit(&NUTZLAST, memory_order_relaxed)' "$kdir/einheit.c" || {
                echo "HARNESS: gift 9 does not apply -- no relaxed load of NUTZLAST in einheit.c"
                return 0
            }
            sed -i 's/atomic_load_explicit(&NUTZLAST, memory_order_relaxed)/NUTZLAST/' "$kdir/einheit.c"
        fi
        rm -f "$kdir/$MODUL.ko" "$kdir"/*.o
        if ! make -C "$KBUILD" "M=$(cd "$kdir" && pwd)" modules > "$arb/make.log" 2>&1; then
            echo "HARNESS: the mutated module did not build"
            tail -20 "$arb/make.log" >&2
            return 0
        fi
        cp "$kdir/$MODUL.ko" "$arb/bau/$MODUL.ko"
    fi

    if [ "$gift" = 11 ]; then
        # **One kernel call MORE in the runtime**, and nowhere else: the mutation is
        # on the runtime copy inside the build directory, re-made with the `Kbuild`
        # the build wrote, so it carries no second copy of the recipe.
        local kdir="$arb/bau/$MODUL.kmod"
        # *The anchor moved twice already:* until K7 this looked for
        # `#include <linux/printk.h>`, until the C-free lane's C2 for
        # `#include <linux/errno.h>` -- the generated driver includes no kernel header at
        # all. The anchor is now the unit's own include, which the driver cannot lose.
        grep -q '#include "einheit.c"' "$kdir/gabbro_kmodul.c" || {
            echo "HARNESS: gift 11 does not apply -- no include of the unit in gabbro_kmodul.c"
            return 0
        }
        sed -i 's|#include "einheit.c"|#include "einheit.c"\nextern void msleep(unsigned int);|' "$kdir/gabbro_kmodul.c"
        sed -i "s|    (void)$EXIT();|    msleep(0);\n    (void)$EXIT();|" "$kdir/gabbro_kmodul.c"
        grep -q 'msleep(0);' "$kdir/gabbro_kmodul.c" || {
            echo "HARNESS: gift 11 does not apply -- the exit function is not where it looks"
            return 0
        }
        rm -f "$kdir/$MODUL.ko" "$kdir"/*.o
        if ! make -C "$KBUILD" "M=$(cd "$kdir" && pwd)" modules > "$arb/make.log" 2>&1; then
            echo "HARNESS: the mutated module did not build"
            tail -20 "$arb/make.log" >&2
            return 0
        fi
        cp "$kdir/$MODUL.ko" "$arb/bau/$MODUL.ko"
    fi

    # **What the RUNTIME still takes from the kernel** (K7). Every probe, because
    # every probe links a different part of the runtime in -- and it is the count
    # that has to reach 0, not any one probe's.
    symbole_pruefe "$arb/bau/$MODUL.kmod" "$MODUL" "$MARKE_KSYM"

    # **The two STATIC checks over what was built**, for the probe that asks for
    # them. They run after every mutation above, on the build directory itself --
    # so what they measure is the artefact the kernel loaded and not the tree.
    if [ -n "${ABBILDUNG:-}" ]; then
        abbildung_pruefe "$arb/bau/$MODUL.kmod"
        if "$W/instrumente/pruefe-atomar-zugriffe.py" "$arb/bau/$MODUL.kmod/einheit.c" \
                > "$arb/zugriffe.log" 2>&1; then
            echo "HARNESS: atomic accesses ok"
        else
            echo "HARNESS: atomic accesses FAILED"
            grep -A2 '^RED' "$arb/zugriffe.log" | head -3
        fi
    fi

    [ "$gift" = 3 ] && rmmod_zeile="echo \"HARNESS: rmmod ok\""

    rm -rf "$arb/initrd"
    mkdir -p "$arb/initrd/bin" "$arb/initrd/proc" "$arb/initrd/sys"
    cp "$(command -v busybox)" "$arb/initrd/bin/busybox"
    ( cd "$arb/initrd/bin" && for a in sh mount insmod rmmod dmesg grep; do ln -sf busybox "$a"; done )
    cp "$arb/bau/$MODUL.ko" "$arb/initrd/"
    cat > "$arb/initrd/init" <<EOF
#!/bin/sh
/bin/busybox mount -t proc none /proc
/bin/busybox mount -t sysfs none /sys
echo "HARNESS: begin"
/bin/busybox insmod /$MODUL.ko && echo "HARNESS: insmod ok" || echo "HARNESS: insmod FAILED"
$rmmod_zeile
/bin/busybox dmesg | /bin/busybox grep -E "gabbro|Oops|BUG:|WARNING:"
echo "HARNESS: end"
/bin/busybox poweroff -f
EOF
    chmod +x "$arb/initrd/init"
    ( cd "$arb/initrd" && find . | cpio -o -H newc 2>/dev/null | gzip -9 > "$arb/initrd.gz" )

    timeout "$FRIST" qemu-system-x86_64 -kernel "$VMLINUZ" -initrd "$arb/initrd.gz" \
        -append "console=ttyS0 quiet panic=1" -nographic -m 512 -no-reboot \
        -smp "$SMP" 2>&1 | tr -d '\r'
}

# -- the verdict over one run --------------------------------------------------
beurteile() {   # $1 = output file, $2 = gift number or "", $3 = probe
    local aus="$1" gift="$2" fehler=0
    probe_waehle "$3"
    local erwartet="$ERWARTET"
    [ "$gift" = 1 ]  && erwartet="$(echo "$erwartet" | sed 's/v=33/v=34/')"
    [ "$gift" = 7 ]  && erwartet="$(echo "$erwartet" | sed 's/gabbro-takt: k=9 v=0/gabbro-takt: k=9 v=1/')"
    [ "$gift" = 10 ] && erwartet="$(echo "$erwartet" | sed 's/k=2 v=512/k=2 v=513/')"

    grep -q "HARNESS: end" "$aus" || { echo "RED: the harness never reached its end (boot or QEMU)"; fehler=$((fehler+1)); }
    grep -q "HARNESS: insmod ok" "$aus" || { echo "RED: insmod did not succeed"; fehler=$((fehler+1)); }
    grep -q "HARNESS: rmmod ok" "$aus" || { echo "RED: rmmod did not succeed"; fehler=$((fehler+1)); }

    # Every expected kernel line, in order, and nothing missing.
    local vorher=0 zeile n
    while IFS= read -r zeile; do
        [ -z "$zeile" ] && continue
        n=$(grep -n -F -- "$zeile" "$aus" | head -1 | cut -d: -f1)
        if [ -z "$n" ]; then
            echo "RED: the kernel log is missing: $zeile"
            fehler=$((fehler+1))
        elif [ "$n" -le "$vorher" ]; then
            echo "RED: out of order: $zeile"
            fehler=$((fehler+1))
        else
            vorher="$n"
        fi
    done <<EOF
$erwartet
EOF

    # **Did the probe get the chance to measure anything?** For `takt` the answer
    # is a number and not a line: a finished run in which the timer never
    # fired says nothing at all (`W1` -- a run that measured nothing is not a run
    # that passed). Gift 6 is exactly this case.
    if [ -n "${TICKS_MIN:-}" ]; then
        local ticks
        ticks="$(sed -n 's/.*gabbro-takt: ticks=\([0-9]*\).*/\1/p' "$aus" | head -1)"
        if [ -z "$ticks" ]; then
            echo "RED: no tick count in the kernel log -- the run reported no opportunities"
            fehler=$((fehler+1))
        elif [ "$ticks" -lt "$TICKS_MIN" ]; then
            echo "RED: the hardirq timer fired $ticks time(s), fewer than $TICKS_MIN -- a run that finished over that many opportunities is not a measurement"
            fehler=$((fehler+1))
        fi
    fi

    # **Did the consumer ever see the flag set?** The same question `ticks` asks
    # for `takt`: a run in which it never did reports a clean `k=4 v=0` about a
    # branch it never entered, and that is not a measurement (`W1`).
    if [ -n "${GESEHEN_MIN:-}" ]; then
        local gesehen
        gesehen="$(sed -n 's/.*gabbro-atomar: k=3 v=\([0-9]*\).*/\1/p' "$aus" | head -1)"
        if [ -z "$gesehen" ]; then
            echo 'RED: no k=3 line in the kernel log -- the run reported no flag observations'
            fehler=$((fehler+1))
        elif [ "$gesehen" -lt "$GESEHEN_MIN" ]; then
            echo "RED: the consumer saw the flag set $gesehen time(s), fewer than $GESEHEN_MIN -- a clean payload check over that many observations is not a measurement"
            fehler=$((fehler+1))
        fi
    fi

    # **What the runtime hard-wires** (K7): a ratchet, not a wall -- see
    # `symbole_pruefe`. It is checked for every probe.
    grep -q "HARNESS: kernel symbols ok" "$aus" || {
        echo "RED: the runtime's kernel calls moved:"
        grep -A4 "HARNESS: kernel symbols FAILED" "$aus" | head -5 | sed 's/^/     /'
        fehler=$((fehler+1))
    }

    # **The two static checks over the built artefact** (K6): the mapping's rows
    # and every access going through them. Their answers travel in the run's own
    # output as `HARNESS:` lines, so this reads them the same way it reads
    # `insmod ok`.
    if [ -n "${ABBILDUNG:-}" ]; then
        grep -q "HARNESS: mapping ok" "$aus" || {
            echo "RED: the atomic mapping did not hold:"
            grep "HARNESS: mapping FAILED" "$aus" | head -4 | sed 's/^/     /'
            fehler=$((fehler+1))
        }
        grep -q "HARNESS: atomic accesses ok" "$aus" || {
            echo "RED: an access to an atomic stands beside the mapping:"
            grep -A3 "HARNESS: atomic accesses FAILED" "$aus" | head -4 | sed 's/^/     /'
            fehler=$((fehler+1))
        }
    fi

    # No oops, no warning, no BUG -- the module left the kernel as it found it.
    if grep -qE "Oops|BUG:|WARNING:|general protection|kernel NULL pointer" "$aus"; then
        echo "RED: the kernel complained:"
        grep -E "Oops|BUG:|WARNING:|general protection|kernel NULL pointer" "$aus" | head -5
        fehler=$((fehler+1))
    fi
    echo "FEHLER=$fehler"
}

ARB="$(mktemp -d "${TMPDIR:-/tmp}/gabbro-kmod.XXXXXX")"
if [ "$KEEP" = 0 ]; then trap 'rm -rf "$ARB"' EXIT; fi

if [ -z "$GIFT" ]; then
    echo "== Gabbro units as Linux kernel modules, in QEMU =="
    echo "   kernel      $VMLINUZ ($KERNVERSION headers)"
    gesamt_fehler=0
    for p in $PROBEN; do
        probe_waehle "$p"
        echo
        echo "-- probe $p: $MODUL"
        echo "   source      $QUELLE"
        echo "   own C       ${FREMD:-(none -- Gabbro only)}"
        [ -n "$VORRAT" ] && echo "   provision   $VORRAT bytes (the program's ceiling is max 4096 slots)"
        mkdir -p "$ARB/$p"
        lauf_einmal "" "$ARB/$p" "$p" > "$ARB/$p/aus.txt"
        grep -E "HARNESS:|gabbro" "$ARB/$p/aus.txt" | sed 's/^/   /'
        ergebnis="$(beurteile "$ARB/$p/aus.txt" "" "$p")"
        echo "$ergebnis" | grep -v '^FEHLER=' || true
        n="$(echo "$ergebnis" | sed -n 's/^FEHLER=//p')"
        gesamt_fehler=$((gesamt_fehler + n))
    done
    echo
    if [ "$gesamt_fehler" = 0 ]; then
        echo "GREEN: halde  -- loaded, allocated, refused on full, reported, unloaded clean."
        echo "GREEN: takt   -- a masks-irqs lock held across a long section, a hardirq timer"
        echo "                 taking the same lock, fired and never landed inside (the run finished)."
        echo "GREEN: atomar -- two DECLARED roots as kthreads, a counter that answers 512"
        echo "                 exactly, a release/acquire flag seen set, a payload never"
        echo "                 stale, two bits ORed to 3; and the mapping's 16 rows expanded"
        echo "                 and held against their builtin and ordering."
        exit 0
    fi
    echo "RED: $gesamt_fehler finding(s)."
    exit 1
fi

# -- the poison runs -----------------------------------------------------------
if [ "$GIFT" = all ]; then
    LISTE="$(gifte)"
else
    LISTE="$GIFT"
fi
gefangen=0
gesamt=0
for g in $LISTE; do
    gesamt=$((gesamt+1))
    arb="$ARB/g$g"
    mkdir -p "$arb"
    p="$(gift_probe "$g")"
    lauf_einmal "$g" "$arb" "$p" > "$arb/aus.txt"
    ergebnis="$(beurteile "$arb/aus.txt" "$g" "$p")"
    n="$(echo "$ergebnis" | sed -n 's/^FEHLER=//p')"
    # **A gift that did not APPLY is not a gift that was caught** (server lane,
    # 2026-09-28). A mutation whose target has moved leaves the run with no QEMU
    # boot at all, and every line of the expectation is then missing -- which
    # reads as a fat catch and measures nothing. *Gift 8 did exactly this the
    # first time it ran: 11 findings, and not one of them about the mapping.*
    # The twin trap is already recorded (a gift that does not apply looks like a
    # pass, gift 5, session 4); this is the same fact from the other side.
    if grep -qE "does not apply|does not measure" "$arb/aus.txt"; then
        echo "GIFT $g: DOES NOT APPLY -- the mutation measured nothing, so its red says nothing"
        grep -E "does not apply|does not measure" "$arb/aus.txt" | head -1 | sed 's/^/    /'
    elif [ "$n" = 0 ]; then
        echo "GIFT $g: NOT CAUGHT -- the harness stayed green under the mutation"
    else
        echo "GIFT $g: caught ($n finding(s))"
        # The indented lines belong to the `RED` above them -- a verdict that
        # printed only the headline would hide WHICH row of the mapping moved.
        echo "$ergebnis" | grep -E '^RED|^     ' | head -5 | sed 's/^/    /'
        gefangen=$((gefangen+1))
    fi
done
echo
echo "gifts: $gefangen of $gesamt caught"
[ "$gefangen" = "$gesamt" ]
