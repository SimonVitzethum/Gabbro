# MUSE-REPORT-601: Flag dependencies across actual decoded control flow

## Task
Lane 601: connect canonical `Flags`/`bedingung`/`Codec.decode` and the actual
subsequent `jumpIf32` (`Ausfuehrung.schritt`) or accepted ControlCodec byte step
to a reusable finite condition dependency check. Consumer connection for
InstructionSelection600, not a parallel CFG or optimiser.

## What was done
New file `grammatik/Grammatik/X86/FlagDependencies.lean` (531 lines) plus one
umbrella import line in `grammatik/Grammatik.lean`. No existing file touched,
no existing theorem weakened.

### New definitions
- `FlagName` (`cf | pf | zf | sf | of_`): AF absent by construction.
- `liestFlag : Bedingung → FlagName → Bool`: read set derived from the actual
  condition value (o/no→OF, b/ae→CF, e/ne→ZF, be/a→CF+ZF, s/ns→SF, p/np→PF,
  l/ge→SF+OF, le/g→ZF+SF+OF).
- `flagWert : FlagName → Flags → Bool`: projection out of a snapshot.
- `stimmtUebberein (c) (f g) : Prop`: agreement on exactly the read flags.
- `jccZiel`: executed control successor (post-decode RIP plus sign-extended
  displacement iff the condition holds) — the `rip` the accepted
  `schritt_jumpIf32_*` equations write.
- Witness states/programs: `sAnder`, `witArith`, `witStart`, `progVor`
  (movImm/store/sub at canonical lengths 10/8/3), `witMovReg`, `witMovStart`.

### New theorems (all premises used, no Prop-typed premises)
- `bedingung_stabil`: read-flag agreement fixes the condition value, all 16
  conditions (axioms: propext).
- `jccZiel_stabil`: same agreement gives the same successor address.
- `decodeJumpIf_laenge`: successful `decode` of a `jumpIf32` shape consumes
  exactly 6 bytes — proved through accepted `DecodingCoverage.decode_abdeckung`
  + coverage shape `decktAb` (no second decoder inversion).
- `jccSchritt_stabil` (main consumer): agreement on the read flags of an
  actually decoded `jumpIf32` implies the same executed `schritt` successor
  RIP, taken and untaken. `hdec` is load-bearing (fixes length/`laengeOk`).
- `cmovBytes_stabil`, `setccBytes_stabil`: same agreement gives the same
  selected word / low byte through accepted ControlCodec byte steps.
- `bedingung_af_frei`: AF may always change; plus 6 concrete group pins
  (`pin_o_ignoriert_cf`, `pin_b_ignoriert_of`, `pin_e_ignoriert_rest`,
  `pin_l_kombiniert`, `pin_g_braucht_null`, `pin_p_ignoriert_sf_cf`).
- `jccSchritt_stabil_zeuge`: JOINT witness — canonical `je +16` bytes decode
  at length 6, two snapshots agreeing on ZF only, both steps run with shared
  successor (via the main theorem itself), preceding run stores 42 observably
  and sets ZF by `sub`, truncated 5-byte prefix refused.
- `mov_xor_wechsel_zeuge`: NEGATIVE witness — MOV keeps ZF clear so `je`
  falls through to 4105; XOR of equal words sets ZF so the same `je` is
  taken to 4121.
- `jccLaenge_verweigert` (bad length refuses, generic), `jccKurz_verweigert`
  (5-of-6 bytes refused). CUTS block + `#print axioms` for every main theorem.

## Evidence
- `./lean-probe grammatik/Grammatik/X86/FlagDependencies.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`
  (Build completed successfully, 440 jobs).
- Axioms: propext / Quot.sound only (`bedingung_af_frei`: none). No `sorry`,
  `admit`, `axiom`, `native_decide`, `unsafe`.
- Producer interfaces reused (nothing duplicated): `Wort.bedingung`,
  `Codec.decode`/`roundtrip_jumpIf32`, `Ausfuehrung.schritt` +
  `schritt_jumpIf32_genommen/nicht` + `zeugeGleich`/`zeugeFlags`/`zeugeSpeicher`
  + `schritt_laenge_verweigert`, ControlCodec `cmovAnwenden_*_wert`,
  `setccSchrittBytes_wert`, `DecodingCoverage.decode_abdeckung`/`decktAb`.

## Open / not claimed (see CUTS in file)
No hardware correspondence, no liveness analysis, no optimiser claim, no
TSO/GX/concurrency/cost/time/termination, no source/checker/Spec/goal claim.

## Notes on the task text
- InstructionSelection600 does not exist yet in the tree (no file found); the
  consumer interface is `stimmtUebberein` + `jccSchritt_stabil` /
  `cmovBytes_stabil` / `setccBytes_stabil` with exact names above.
- Inhabitation rule: no theorem here quantifies over program syntax
  (`Vertrag`/`Stmt`/`Endblock`/`ErgExpr`/`Expr`/`Args`), so no mechanical
  `_zeuge` was required; joint witnesses are provided anyway as the task asks.

## Useful next independent tasks (exact ownership, not started)
- InstructionSelection600 (whoever owns it): consume `stimmtUebberein` as the
  flag-liveness/refinement check for select lowering; needs no change here.
- A `byteschritt`-level (fetch+decode+execute from memory) lifting of
  `jccSchritt_stabil` reusing `Byteschritt.fetchDekodiert`: independent,
  disjoint follow-up.
