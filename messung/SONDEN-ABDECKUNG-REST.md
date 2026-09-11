# Probe coverage remainder after the frist-28 staffel binding

Status: measurement, not a verdict. Base `8393dc0`, branch `m03-sondenabnahme`,
worktree `.claude/worktrees/m03` only. All counts below live in code spans, so no
counting guardian reads this file as a register (the `FRIST-SONDEN-28.md` precedent).

## 1. The acceptance chain that owns probe coverage

Two runners share the work, and the figure lives in only one of them:

- `instrumente/pruefe-sonden.sh` RUNS probes: every `sonden/sonde_*.c` is built with
  the runner's flags and judged under the probe contract (`0` holds, `1` refutes,
  `77` not runnable here). It measures THAT a probe runs, not WHAT it refutes.
- `instrumente/pruefe-sondendeckung.py` KEEPS the register: `A_p` = falsifiable
  assumptions whose named probe stands as a program in `sonden/`, over falsifiable
  assumptions. Recomputed for this post: `17` of `50`, `A_p = 0.3400` against booked
  `17/50` and floor `1/8`, `ALL PASS`, exit `0`.
- `instrumente/abnahme.py` drives both: it auto-discovers every
  `instrumente/pruefe-*.sh` / `pruefe-*.py` by glob (no list to rot), so both runners
  are standard acceptance, quick run included (neither is in `SCHWER`).
- `instrumente/pruefe-zahlen.py` pins the figure: it recomputes `A_p` numerator and
  denominator from the coverage runner and holds them against `dokumente/PLAN.md`
  and `dokumente/SONDENDECKUNG.md`.

The `14` staged probes under `messung/proben/frist-28/` stood outside all of this
("staged: in keiner Abnahme"): the probe runner globs only `sonden/sonde_*.c`, and
the coverage runner counts only obligations with programs.

## 2. Binding performed: the staffel stage

Binding location: the final stage of `instrumente/pruefe-sonden.sh`
(`Frist-28 staffel`), appended, no existing line reworded. It runs
`messung/proben/frist-28/run.sh` under the runner's own `FRIST` (`120` s; the staffel
measures about `2` s on `fisch`), prints the per-probe verdicts indented, and
requires exit `0` plus the `FRIST-28: ALL PASS` marker — else `FINDING`, exit `1`.
The stage stands last with nothing behind it, so that `exit 1` is a complete
finding about the staffel, not a cut.

Evidence:

- Full runner, local scoped run with the `free -g` gate (`31` GB total, `11` GB
  available): exit `0` in `7` s; the stage prints all `14` `PASS` lines,
  `FRIST-28: ALL PASS`, `HOLDS`.
- `run.sh` on `fisch` (`gabbro-m03`): `FRIST-28: ALL PASS`, exit `0`, `2` s wall.
- Stage logic both directions (byte-identical lines, stubbed runner path): real
  `run.sh` gives `HOLDS` / exit `0`; a stub exiting `1` gives `FINDING` / exit `1`;
  a stub exiting `0` without the marker gives `FINDING` / exit `1`.
- Coverage recompute after binding: `17` of `50`, `ALL PASS`, exit `0` — no figure
  moved, which is the honesty check (section 3 says why it must not).

Known pre-existing red on `fisch`: the full runner exits `1` there with `4`
refuted (`sonde_barriere`, `sonde_byte_legen`, `sonde_ruf_verteiler`,
`sonde_speicher_schranke`) — exactly the four `FRIST-SONDEN-28.md` documents as
`Tux`-booked tripwires against the `fisch` distribution (two flaky, two systematic
by one frequency quantum). That post books their rebooking at the owning lane and
does not rebook them; neither does this one. The staffel itself is green on
`fisch` (`run.sh` exit `0` above); the staffel stage is reached end to end where
the `sonden/` loop is green (local run above).

## 3. Why `A_p` stays `17` of `50`: the runner cannot take them

Moving `A_p` is not a runner edit. One covered assumption is four moves at once
(the `SONDEN-ROWS-72.md` recipe, executed by owner assemblies for every earlier
lane):

1. a `deadline` clause in `beispiele/*.gab` declaring the obligation
   (`frist_<fn>_eingehalten`), which grows the assumption census;
2. a program `sonden/sonde_*.c` carrying the probe name;
3. an entry in `manifest::SONDEN_MIT_PROGRAMM`
   (`crates/gabbro-check/src/manifest.rs`), without which the checker strikes the
   name and tooth `10` fires;
4. a register row in `dokumente/SONDENDECKUNG.md` plus the quota-mark move and the
   speech-tooth updates in `instrumente/pruefe-sondendeckung.py`.

The staged probes arrive with none of the four: no `deadline` clause names their
`14` obligations, no `sonden/` copy exists, no manifest entry lists them. Moves
`1` and `3` are outside this post's scope — `beispiele/` edits move the
assumption census and the emission corpus, and `manifest.rs` is checker logic.
Counting staged files as covered without obligations behind them would be fake
coverage, so the staffel binds the RUN and leaves the QUOTA untouched.

Arithmetic note, reported as found: the mission brief counts `11` new probes and
`A_p` `17 -> 28`. The merged tree carries `14` staged probes (`10` timed green,
`4` exiting `77`), and full binding of all `14` would read `31` of `64`, not `28`
of anything. No subset yields `11 -> 28` either (`10` timed would read `27` of
`60`). The remainder below therefore books all `33` uncovered assumptions, not
`22`.

## 4. Remainder: `33` assumptions without a running program

Classes per `dokumente/SONDENDECKUNG.md`: `P1` ring `0` (control register, page
table, MSR, `in`/`out`); `P2` a device (VT-d, virtio, `16550`, timer, counter);
`P3` a mechanism the generator does not emit (grace period, fetching reader,
ending source); `P4` userland (all `17` rows carry `PROGRAM`, nothing open).

### 4.1 `P1`: `14` rows, ring `0` — the bench faults before any timing

Every row needs a ring-`0` bench: `invlpg`, `out`, control registers, MSRs and
page-table writes fault in ring `3`, so no userland program can time the real
path. A stub would be an analogy, which the probe contract forbids.

| assumption | probe | why no program | what it would take |
|---|---|---|---|
| `cr3_leert_den_tlb` | `sonde_cr3_leert_den_tlb` | `write_cr3` faults in ring `3` | ring-`0` bench timing the reload path |
| `gast_bleibt_in_seinem_raum` | `sonde_gastausbruch` | needs a guest (VMX) | a virtualized bench with a guest to attempt escape from |
| `invlpg` | `sonde_invlpg` | `invlpg` faults in ring `3` | ring-`0` bench; adjacent only: `frist28_seite_vergessen` attempts the same instruction but attributes to a new deadline, not to this assumption |
| `kern_bleibt_unter_jeder_aenderung_abgebildet` | `sonde_kern_entmappt` | needs kernel-mapping access | a bench that can unmap and probe from the faulting side |
| `masks_irq_schuetzt_wie_eine_sperre` | `sonde_irq_maskiert` | needs observable interrupt masking | a bench with maskable interrupt source and a preemption detector |
| `mmu_folgt_ihrem_modell` | `sonde_pf_bei_p0` | needs page-table access | a bench that walks and faults pages on demand |
| `neuer_eintrag_verdraengt_nichts` | `sonde_praesent_ohne_invalidierung` | needs TLB-invalidation observation | ring-`0` bench observing stale-entry behavior |
| `portraum_ist_x86` | `sonde_portraum` | needs port-space semantics | a bench with real port IO behind the access |
| `tlb_ist_nach_cr3_leer` | `sonde_tlb_nach_cr3` | `write_cr3` faults in ring `3` | ring-`0` bench as for `cr3_leert_den_tlb` |
| `write_cr0` | `sonde_cr0` | privileged register | ring-`0` bench |
| `write_cr3` | `sonde_cr3` | privileged register | ring-`0` bench |
| `write_cr4` | `sonde_cr4` | privileged register | ring-`0` bench |
| `wrmsr_efer` | `sonde_efer` | privileged register | ring-`0` bench |
| `x2apic_braucht_zwei_schritte` | `sonde_x2apic_braucht_zwei_schritte` | needs APIC MMIO | a bench with x2APIC reachable |

### 4.2 `P2`: `15` rows, a device — no device stands on the bench

Every row needs its device on the bench (VT-d tables, virtio queues, `16550`
UART, timers, counters). The staged userland probes time local workloads, never
device memory, so they attribute to new deadlines, not to these assumptions.

| assumption | probe | why no program | what it would take |
|---|---|---|---|
| `dma_kohaerent` | `sonde_dma_kohaerenz` | no DMA engine on the bench | a bench with coherent DMA and a checker-side observer |
| `dma_sichtbarkeit_in_reihenfolge` | `sonde_dma_reihenfolge` | same | same, with ordered-visibility assertions |
| `dma_veroeffentlichung_braucht_barriere` | `sonde_dma_ohne_barriere` | same | same, plus a barrier-omission arm |
| `geraet_antwortet` | `sonde_geraet_antwortet` | no device behind the dispatch | a bench with a responding device model |
| `geraet_quittiert` | `sonde_vtd_srtp` | no VT-d | a bench with VT-d fault reporting; note the shared probe name with the row below (two obligations, one name) |
| `geraeteregister_veroeffentlicht_wie_ein_atomic` | `sonde_virtio_avail` | no virtio device memory | a bench with virtio `avail` ring memory |
| `karte_antwortet` | `sonde_karte_antwortet` | no card on the bench | a bench with the card model |
| `karte_liest_nach_dem_index` | `sonde_deskriptor_zu_frueh` | same | same, with descriptor-timing observation |
| `uart_leert_sich` | `sonde_uart_leert_sich` | no UART hardware | a bench with a `16550` that drains |
| `virtq_geraet_schreibt_used` | `sonde_virtq_used` | no virtqueue device side | a bench with a device writing `used`; adjacent only: `frist28_used_lesen` times a local read, not the device write |
| `vtd_srtp_quittiert` | `sonde_vtd_srtp` | no VT-d | same bench as `geraet_quittiert`; shared probe name, see above |
| `vtd_te_wirksam` | `sonde_vtd_te` | no VT-d | a bench with translation enable observable |
| `zaehlwerk_antwortet` | `sonde_zaehlwerk_antwortet` | no counter device | a bench with the counter hardware |
| `zeitgeber_meldet_sich` | `sonde_zeitgeber_meldet_sich` | no timer device | a bench with the timer hardware |
| `zeitgeber_tickt` | `sonde_zeitgeber_tickt` | same | same, with tick observation |

### 4.3 `P3`: `4` rows, not emitted — there is no body to time

Every row names a mechanism the generator does not emit (grace period, fetching
reader, ending source/input). Timing a local stub would be an analogy, which the
probe contract forbids — the same position as `queue_arm`/`verteiler` below.

| assumption | probe | why no program | what it would take |
|---|---|---|---|
| `eingabe_endet` | `sonde_eingabe_endet` | no emitted input-end path | the emitter emits the path, or a phase bench the probe may call without inventing one |
| `gnadenfrist_ist_abgelaufen` | `sonde_leser_noch_drin` | grace period is a model-level wait | a bench that can hold and release a reader across the period |
| `leser_holt_ab` | `sonde_leser_holt_ab` | reader fetch is not emitted | same emitter-or-bench decision as `eingabe_endet` |
| `quelle_endet` | `sonde_quelle_endet` | source end is not emitted | same emitter-or-bench decision as `eingabe_endet` |

## 5. Not in the `33`: three dated functions without even a staged probe

These have no `deadline` clause, hence no assumption, hence no denominator share
— future work, not current remainder:

- `queue_arm` (`beispiele/02-geraet.gab`, `costs 8 ops`): `extern`, no body is
  emitted. Needs: the emitter emits the phase-transition body, or a phase bench
  the probe can call without inventing one.
- `verteiler` (`beispiele/60-annahme-mit-maschine.gab`, `costs 8 ops`): `extern`,
  same position as `queue_arm`. Needs the same: an emitted entry body behind the
  dispatch.
- `uart_haengt` (`beispiele/65-port-space.gab`, `costs 1 ops`, never returns,
  `diverges`): a date on a function that never returns cannot be refuted by
  sampling — no run completes, so no percentile ever materializes. Needs: the
  `unfalsifiable` tail with this reason, not a probe that can only hang or lie.

## 6. Recompute commands

On `fisch` in directory `gabbro-m03` (tree synced with `rsync -rlpgoD`,
`beweise/` with `rsync -a`, `PATH=$HOME/.cargo/bin`):

```bash
./instrumente/pruefe-sondendeckung.py
./messung/proben/frist-28/run.sh
./instrumente/pruefe-sonden.sh
./instrumente/pruefe-kennungen.py
./instrumente/pruefe-syntax.sh
```

Expected: coverage `17` of `50`, `ALL PASS`, exit `0`; staffel `FRIST-28: ALL
PASS`, exit `0`; probe runner exit `0` where the `sonden/` loop is green (locally
measured; on `fisch` the loop stands at `4` documented refutations, section `2`).

## 7. Guardian impact

One runner appended to, one file created, nothing else touched: no `.gab` added
or changed (assumption census untouched), no `sonden/` file added or changed
(program column untouched), no `manifest.rs` entry (checker logic untouched), no
`.lean` touched, no German cell rephrased (the appended stage is new English
text; the verdict words it adds are new lines, not rewordings). Numbers in this
file live in code spans only.
