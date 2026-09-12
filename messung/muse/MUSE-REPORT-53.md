# MUSE-REPORT-53: The call machine with local environments (attempt F)

Lane 53, branch `muse/53`. New file `grammatik/Grammatik/RufMaschineF.lean`
(+ import line in `grammatik/Grammatik.lean`). No existing file edited.
`RufMaschineD.lean` untouched (copied shape, own design).

## What I did

Built the call machine with per-frame local environments, fixing both
defects from the REVIEWER NOTE on `RufMaschineD.lean`:

1. **Frames carry their current-context environment.** `RufRahmenF.rest`
   is `Sigma l Gamma Lambda, Env D Gamma x Endblock D (vertragVon D f)
   l Gamma Lambda`: the stored `rho` sits next to the residue. `blatt`
   runs `execStmt O passes keinRuf s (M.weltVon f) rho` with the STORED
   `rho` and stores the resulting `rho'` (the `.ok sigma' rho'` outcome,
   matched as an equation `hstep`, not only `.welt`). `ruf` evaluates the
   arguments in the caller's stored `rho` (`hrho : rho = evalArgs s0 args
   s0 rho`). `rueck` evaluates the result in the callee's stored `rho`
   (`hv : v = hfg |> evalErg s1 e s1 rho`). No step constructor binds a
   free environment.
2. **Keyed stack/log invariant with proved preservation.** `RufSchluesselF`
   projects a frame to `(function, parameter rho, entry world)`; the
   residue and local context are NOT part of the key, so `blatt` (which
   advances the residue and the stored local env) preserves the key stack
   definitionally. `RufLogPasstF` is the D-shaped log derivation over key
   stacks; `rufLogPasstF_gedeckt` gives return fidelity for well-formed
   logs; `rufSchrittF_passt_acting` (per-constructor case split) plus
   `rufSchrittF_passt_anders` (untouched threads via `rufUpdateF_noteq`)
   give `rufSchrittF_passt`; induction gives `rufErreichbarF_passt`.

TARGET proved with the exact fixed statement (binder order `P O passes sp
init M h f`, conclusion `forall g rho v s0 s1, rueck ... mem -> eintritt
... mem`):

- `rufF_treu` (`RufMaschineF.lean`, via `rufErreichbarF_passt` +
  `rufLogPasstF_gedeckt`).

ZEUGE (`rufF_treu`): `rufF_treu_zeuge` instantiates ALL premises JOINTLY
with concrete values on a NON-DEGENERATE program: one table (`rufDF`,
`count 2`, one `.int 0 5` field) that the callee writes, and a THREE-STEP
run reached FROM THE START STATE (`reach3F_start : RufErreichbarF rufPF
rufOF 0 (RufStartF rufPF spF initF) M3F`): `ruf` (caller `false` calls
callee `true`, step `schritt1F`), `blatt` (writing leaf `leafSF` runs
`assignSlot` under stored `rufRhoF`; slot 0 moves 0 -> 2 by
`outWF_moves`, step `schritt2F`), `rueck` (pops the callee, logs `rueck`
with entry world, step `schritt3F`). `M3F_log` names the full log
(return, callee entry, caller entry).

## Exact names of new definitions/theorems

Machine: `RufEreignisF`, `RufRahmenF`, `RufFadenF`, `RufMaschineF`,
`RufMaschineF.weltVon`, `RufFreiF`, `rufEigenF`, `rufUpdateF`,
`rufUpdateF_self`, `rufUpdateF_noteq`, `RufSchrittF`, `RufStartF`,
`RufErreichbarF`. Invariant: `RufSchluesselF`, `RufFadenSchluesselF`,
`RufLogPasstF`, `RufFadenPasstF`, `rufRueckGedecktF`,
`rufLogPasstF_mem_eintritt`, `rufLogPasstF_eintritt_mem`,
`rufLogPasstF_gedeckt`, `RufFadenSchluesselF_ruf`,
`RufFadenSchluesselF_blatt`, `RufMaschinePasstF`, `rufStartF_passt`,
`rufSchrittF_passt_acting`, `rufSchrittF_passt_anders`,
`rufSchrittF_passt`, `rufErreichbarF_passt`, `rufF_treu`. Witness:
`rufDF`, `rufCallerF`, `rufIncF`, `rufDF_erg`, `rufDF_params`,
`rufRhoF`, `rufVF` (unused, see CUTS), `rufRumpfF`, `rufHpF`,
`rufArgsF`, `rufCallerRumpfF`, `rufPF`, `rufOF`, `rufWeltF`,
`leafSF`, `restF`, `rufRumpfF_eq`, `leafSF_blatt`, `leafSF_mem`,
`rhoCallerF`, `initF`, `initF_rho`, `M0F`, `M0F_kopf`, `M0F_fun`,
`callerParamsF`, `M0F_kopf_alt`, `outWF`, `leafSF_ok`, `outWF_moves`,
`anfangF_leer`, `heldLeerF`, `M1F`, `argsOrteF`, `schritt1F`, `reach1F`,
`eF`, `restF_eq`, `eF_orte`, `vF`, `vF_wert`, `M2F`, `M1F_kopf`,
`M1F_welt`, `schritt2F`, `reach2F`, `M3F`, `schritt3F`, `reach3F`,
`M0F_start`, `reach3F_start`, `M3F_log`, `rufF_treu_zeuge`.

## Last `./lean-bau` result line

`Build completed successfully (37 jobs).` (`./lean-probe
grammatik/Grammatik/RufMaschineF.lean`: `0 error(s) in the COMPLETE
output`; all `#print axioms` show only `[propext, Classical.choice,
Quot.sound]`.)

## What remains open

See the `CUTS:` block at the end of `RufMaschineF.lean`: partial machine
(no compound-statement steps), no contract discharge (`ReqAmEintritt` /
`EnsAmRueck` not wired to the events), stale one-function leftovers
(`rufVF`, `rufWeltF`, `M0F_kopf_alt`). Rule 13 note: `rufF_treu` itself
has no universal premise over program syntax (its only premise besides
data is the reachability `h`), so no `_zeuge` is needed beyond the named
TARGET witness, which is provided.

## Anything in the task I believe is wrong

Nothing material. Two friction points, both handled, neither a task
defect: (1) `cases init f with | mk g rho => rfl` leaves `(⟨g,rho⟩).1`
projections that `rfl` does not unfold -- keep the `init f = ⟨g,rho⟩`
equation and rewrite the `match` in `RufStartF` instead (`rufStartF_passt`,
`M0F_kopf`); (2) `cases hs with | rueck <21 names>` misaligns because the
`_` placeholder constructor field is not a case binder (22 binders for
`rueck`, 16 for `blatt`, 4/2 for `nimmt`/`gibt`, 17 for `ruf`, 6 for the
`schritt` reachability case) -- the untouched-thread lemma uses `cases hs
<;> (subst_vars; simp_all [rufUpdateF_noteq])` which is immune to the
count. Also: `instrumente/pruefe-praemisse.py` needs `ki-pc-fisch-101`
over ssh, which does not resolve from this host, so premise-necessity was
checked by reading (every premise of every theorem is used; no `Prop`-typed
premise, no `intro _`, no `have _ :=`, no `sorry`/`admit`/`axiom`).
