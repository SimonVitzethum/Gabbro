# MUSE-REPORT-1329: TSO projection for the rest tags

Lane 1329, clone `/home/simon/Dokumente/gabbro-muse/a1329`, branch `muse/1329`.
New file `grammatik/Grammatik/X86/HwKapsteinTsoRest.lean` (745 lines) plus one
`import Grammatik.X86.HwKapsteinTsoRest` line in `grammatik/Grammatik.lean`.
Nothing else touched.

## What was done

Classified my ten union tags of `HwVollSchritt` against the TSO projection
`kapTso` (lane 1295 vocabulary reused, never copied):

- **uc** (`rest_uc_still`, `rest_union_uc`): projection-unchanged (admitted
  stores step to the same machine, loads never admit). Device effect named
  alongside: `rest_uc_geraet` (posted write plus log on the extended machine).
- **port** (`rest_port_still`, `rest_union_port`): projection-unchanged (core
  data only). Bus effect named: `rest_port_bus` (reached generic bus step
  with the accepted latch answer).
- **fp** (`rest_fp_tso`, `rest_union_fp`): all 7 legs — register legs silent,
  loads observe with forwarding, stores single `issueByte`, drains single
  `flushKern`, refusals silent.
- **fehler** (`rest_fehler_tso`, `rest_union_fehler`): embedded steps reuse the
  base leg, fault outcomes silent self-loops.
- **tor** (`rest_tor_still`, `rest_union_tor`): admitted legs re-embed core
  data only, refused legs self-loop.
- **vec** (`rest_vec_speicher_erreichbar`, `rest_vec_tso`, `rest_union_vec`):
  register/load/refusal legs silent, stores fold sixteen `issueByte` events
  (no whole-vector atomicity).
- **bild / instanzen** (`rest_integer666_still`, `rest_union_bild`,
  `rest_union_instanzen`): the register-path plug moves core data only.
- **nested / int**: proved buffer silence for every successful single and
  nested delivery (`rest_asyncFertig_puffer`, `rest_async_puffer_still`,
  `rest_int_puffer`, `rest_nest_puffer_still`, `rest_nested_puffer`),
  exhibited refusals (`rest_int_verweigert`), and the sharp FINDING
  (`rest_int_befund`, see below).
- Joint summary `rest_acht_tso` (8 reaching tags) and joint witness
  `rest_zeuge` (one exhibited union step per rest tag, reachability for the
  eight, delivery buffer silence plus memory change, owner-only forwarding
  with foreign staleness and drain-into-memory, delivery refusals).

## Verification

- `./lean-probe` green after every addition (0 errors).
- Full `./lean-bau`: `Build completed successfully (691 jobs).`
- `#print axioms` for all 27 theorems: `[propext]` or
  `[propext, Quot.sound]` only — subset of the goal-allowed set, no
  `Classical.choice` needed, no `sorry`/`admit`/`axiom`/`native_decide`/
  `unsafe` anywhere (two comment occurrences of the English word "admit"
  only, verified by word-boundary grep).
- No premise has type `Prop` itself; every theorem premise is used by its
  proof (checked by hand; refusal-branch closures use their hypothesis).

## What remains open (FINDINGs)

1. **nested/int have no `TSOErreichbar` leg (high priority).** Successful
   delivery installs direct-pushed memory (`schiebeRahmen`/`write64`) with
   untouched buffers, so the per-access target-to-W/GX bridge needs a
   drained-own-buffer guard for delivery (or delivery as serialising context
   switch). Proved: general buffer silence (single, nested, adapter levels),
   exhibited NMI memory change with still buffers, exhibited refusals.
2. The six other tags (lockRmw, isa, addr, muldiv, lockFetch, system) belong
   to other lanes. No W/GX bridge, no atomicity beyond the folds, no
   hardware correspondence beyond self-consistency (see file CUTS block).

## What I believe is wrong in the task

The per-tag instruction for nested/int ("the interrupt frame is pushed
through the buffer as the interrupt lane models; classify it as the
stack-push events") is factually wrong about the lane model and was
declined with reason: S3 in `HwNestedInterrupts.lean` states delivery is
explicitly NOT a buffer drain; `asyncMasch_puffer_still` proves buffers
untouched; the frame path is `schiebeRahmen` over direct `write64` pushes;
and the accepted NMI witness provably changes memory (`witNmi_aendert_ss`)
while no buffer grows (`witNmi_puffer_0/1`). Classifying delivery as
stack-push buffer events would assert a falsehood; per the task's own rule
("a step that writes memory by a path other than the TSO events is a
FINDING of high priority") it is recorded as the sharp FINDING
`rest_int_befund` instead. Suggest the coordinator correct the task text
for any follow-up lane.
