# MUSE-REPORT-51 (lane 51, REFERENCE FIXTURE attempt B of 2)

## What was done

New file `grammatik/Grammatik/ReferenzB.lean`, wired into the build as the
last import of `grammatik/Grammatik.lean`. All in namespace
`Gabbro.Grammatik`, English only, no `sorry`/`admit`/`axiom`/`native_decide`/
`unsafe`, `./lean-bau` green for the whole project (37 jobs).

1. Declaration `refD`: `Tab = Unit` (one table `konto`, `count = 2`, one
   field `()` of type `.int 0 100`), `Lock = Unit` (one lock `m`),
   `braucht () = [.inl ()]`, `geteilt = true`, `Fn = Bool`
   (`einzahlen = true`, `lies = false`). Signatures: `refSigEin`
   (`params [.int 0 10]`, `erg none`, `haelt [()]`, writes) and
   `refSigLies` (`params []`, `erg (some (.int 0 100))`, `haelt [()]`,
   no writes). Shape follows `miniContrD` (`VertragOrtB.lean`) and `rufD`
   (`RufMaschineD.lean`).
2. Contracts: `einzahlen` requires `true` (`refReqEin`), ensures
   `old(konto[0]) <= konto[0]` (`refEnsEin`, `altSlot <= slot`);
   `lies` requires `true` (`refReqLies`), ensures `result = konto[0]`
   (`refEnsLies`). Bodies: `refRumpfEin` is `konto[0] := 100; call lies;
   ret` (constant cap, the upper branch of the task's `min`), `refRumpfLies`
   is `ret konto[0]`. Program `refP`; rewrite `refEin_start`/`refLies_start`
   casts bridge the definitional `[held]` vs signature-holding mismatch.
3. Oracle `refO` (empty domains) with `refO_gut` proved by `nomatch`;
   start memory `refSp0` (both slots `0`) with `refSp0_slot`.
4. Call-machine run from `refM0B = RufStartD refP refSp0 refInitB`
   (thread 0 runs `lies`, thread 1 runs `einzahlen 7` via `refRho7`):
   step A `nimmt` (`refSchrittA`, `refReachA`), step B writing `blatt`
   `konto[0] := 100` (`refSchrittB`, `refReachB`), step C `ruf` of `lies`
   (`refSchrittC`, `refReachC`). All premises proved, all used.
5. PC side: `refProgB` (thread 1 leaf atom with lock holdings and carrier
   `[.inl ()]`), `refPC1pre` (hand-built machine with the lock taken),
   `refPCschritt : PCSchritt ...` (leaf fires, `hmark`/`hcar` proved),
   `refPCschreibt` (slot reads `100`) and `refPCschreibt_zeuge`
   (`100 /= 0`, memory really moved).

## Exact names of new definitions/theorems (selection)

`refSigEin refSigLies refD refEin refLies refEin_params refEin_erg
refLies_params refLies_erg refRho7 refEin_schreibt refLies_schreibt
refLies_haelt refLies_gruende refEin_ende refLies_ende refDarf refDarfEin
refDarfLies refIdxEin refIdxLies refHundert refReqEin refEnsEin
refIdxEnsLies refReqLies refEnsLies refEin_start refHpLiesAt refArgsLies
refWriteSt refWriteStAt refRumpfEin refLies_start refIdxBodyLies
refDarfBodyLies refRumpfLies refP refO refO_gut refSp0 refSp0_slot
refP_rumpf_ein refP_rumpf_lies refInitB refM0B refFrei0B refSelf0B
refRang0B refM1B refSchrittA refReachA refM1kopf refM1rho refM1haelt
refK0 refV100 refM2B refM1rest refSchrittB refReachB refM3B refM2haelt
refSchrittC refReachC refCallerB refM3kopf refM3s0 refV100back refM4B
refM3rho refM3rest refProgB refPC0 refPC1pre refPCwrite refPC1haelt
refPC2 refPCschritt refPCschreibt refPCschreibt_zeuge`.

## Last `./lean-bau` result line

`Build completed successfully (37 jobs).` with
`== 0 error line(s) in the COMPLETE output`.
`./lean-probe grammatik/Grammatik/ReferenzB.lean`: `0 error(s)`.

## What remains open (task items NOT delivered)

- `refB_erreicht : RufErreichbarD refP refO passes (RufStartD refP sp init) MB`
  and `refB_schreibt`: the run stops at step C (`refReachC`). Step D
  (`rueck`, `refSchrittD`/`refM4B` drafted then reverted to keep the build
  green) is unproved.
- `refB_pc_erreicht` / `refB_pc_schreibt`: only a single `PCSchritt` from a
  hand-built pre-machine (`refPCschritt`) plus the memory fact; no
  `PCReach ... (GenStart sp0)` chain exists.
- No `<name>_zeuge` companions for `refB_schreibt`/`refB_pc_schreibt`
  exist, since the targets themselves do not exist. `refPCschreibt_zeuge`
  is the only memory-moved witness.
- Export names `refD refP refO refO_gut refSp0` exist; the two runs do not.

## Believed-wrong points and precise blockages (measured, not suspected)

1. `rueck` blockage (1): `(refM2B.faeden 1).kopf = refCallerB` is false as
   stated. `refCallerB.s0` is the world at the call (`refM2B.weltVon 1`),
   but `(refM2B.faeden 1).kopf.s0` is the pre-write entry world; step B
   (`schreibSlot`) moved the world in between. The popped-frame
   projection must carry the entry world through the write, or the caller
   frame must be named with the post-write world. Design fact, not a model
   gap.
2. `rueck` blockage (2): `ErgExpr.orte` of the `lies` return is
   `[.inl ()]`, not `[]` (slot read carries its carrier). So `hs1`
   (return world = thread world) is false: the return emits a read event,
   and `hv` (value = `100`) needs the post-write slot fact through that
   read world. Same class: the body reads what the previous step wrote.
3. PC staging: `refPC1pre` is hand-built. The `nimmt` pre-step has no
   `GenErreichbar`/`PCReach` derivation from `GenStart`, so there is no
   `refB_pc_erreicht` yet. Positive finding for the task's closing
   question: a leaf CAN write under `PCSchritt` for a checker-shaped
   program (`refPCschritt` fires with `hmark`/`hcar` proved) -- no premise
   blocks it.
4. No universal premise over `Vertrag`/`Stmt`/`ErgExpr` was added, so rule
   13 needs no companions in this file; the ZEUGE targets
   (`refB_schreibt`, `refB_pc_schreibt`) are not present to witness.
