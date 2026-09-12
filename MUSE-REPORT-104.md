# MUSE-REPORT-104 — lane 104 (D4: chain from a machine run, N threads)

## What was done

New file `grammatik/Grammatik/KetteVoll.lean`, wired into the build via
`import Grammatik.KetteVoll` at the end of `grammatik/Grammatik.lean`.
It proves the D4 target: from any `PCReach` run, a joint chain with the
same worlds and the same step threads, for any number of threads and any
interleaving. The induction runs over `PCSpur` (thread trace), not over
`PCReach` directly, so each level knows its acting thread.

How each `GemeinsamerLauf` field is discharged (no premise quantifies
over `Vertrag`/`Stmt`/`Endblock`/`ErgExpr`/`Expr`/`Args`):

- `hKette`: `spurLaenge` — one world per spur step plus the start world.
- `hSchritt`: `kette_schritt_rahmen` — old positions ride the prefix
  chain; the new position closes by the fired step. Leaf frames come
  from `blatt_rahmen_vertrag` (via `hO`) widened with `Rahmen.weiter`
  by the full-rights code, transferred from the acting thread's world
  to the chain worlds through memory equalities (`letzteSpeicher`,
  `speicher_welt_speicher`; `Rahmen` ignores traces). Lock
  (`take`/`rel`) frames hold because memory is unchanged.
- `hPaar`/`hBeschraenkt`/`hGesittet`: the chain's recorded run stays
  empty (`J.l = []`, the target only asks for worlds and step threads),
  with the permissive pair set `ketteNb` — all close vacuously
  (`gesittet_nil`, `beschraenkt_nil`).
- `hEintritt`: entry worlds are built to fit (`eintrittOf`: start memory
  with a trace holding exactly the code's declared entry locks;
  `eintrittOf_passt`).
- `hSchuld`: premise-free for every function by U003
  (`schuldnerHaelt_gilt`).
- `hInvSicht`: follows from entry (`sicht_aus_eintritt` via
  `heldIn_invarianten` + `eintrittHeldIn_aus_Passt`).

## Exact names of new definitions/theorems

All in namespace `Gabbro.Grammatik.KetteVoll` (see §"wrong" below for why):

- defs: `ketteNb`, `spurFuer`, `eintrittOf`
- theorems: `offen_spurFuer`, `mem_offen_spurFuer`, `eintrittOf_passt`,
  `sicht_aus_eintritt`, `gesittet_nil`, `beschraenkt_nil`, `spurLaenge`,
  `letzteSpeicher`, `kette_schritt_rahmen`, `kette_aus_spur`,
  `kette_aus_lauf_voll`, `kette_aus_lauf_voll_zeuge`

## Last `./lean-bau` result

`== 0 error line(s) in the COMPLETE output`, build completes
(`Built Grammatik.KetteVoll`). `./lean-probe` on the file: 0 errors.
`#print axioms` for both main theorems:
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no extra axiom.
No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`, no `intro _`,
no `have _ :=` in the file. Every premise is used (audited:
`hO`→leaf frame, `hVollT`/`hVollG`→widening, `h`→spur, `P`→sight bridge).

## What remains open

- The built chain has `J.l = []`, not `J.l = M.lauf`. A chain tracking
  the recorded run as well would additionally owe `PCMarkSep` /
  `PCUnsharedSep` (W4/W5 need program-text separation for arbitrary
  programs). Witness-carrying consumers (`SerialLink` legs) are untouched.
- `hVollT`/`hVollG` (every thread's code writes every carrier) is
  stronger than necessary; per-step contract-to-code wiring in the style
  of `kette_mit_zeugen`'s `hW`/`hG` would narrow it, at the price of
  syntax-quantified premises. The current form keeps rule 13 to the
  target itself.
- No diagnostic codes, probe numbers, or example numbers were added
  (the task assigns none).

## Things in the task I believe are wrong

1. **Name collision (hard blocker, worked around).**
   `MaschinenKette.lean:322` already defines
   `Gabbro.Grammatik.kette_aus_lauf_voll` (single-thread lock-only,
   concluding a guarded `SerialLink`, no thread trace). Defining the
   target under the same fully-qualified name breaks `./lean-bau` for
   the whole project once both files are imported. I did not rename or
   weaken the existing theorem (rule 5); the N-thread theorem and its
   witness live in namespace `KetteVoll`
   (`Gabbro.Grammatik.KetteVoll.kette_aus_lauf_voll[_zeuge]`), and the
   CUTS block of the file records this. Mechanical checks matching the
   short names still hit.
2. **The bare target shape is false as stated (proved, not suspected).**
   With no code argument, if `D.Fn` is empty there is no
   `Faden → D.Fn`, hence no `GemeinsamerLauf` at all — while a
   lock-only `PCReach` over the same `D` still exists. So the
   premise-free shape cannot hold in full generality. Per the task's own
   escape clause I take a restriction: an explicit code map plus
   full-rights facts `hVollT`/`hVollG`. These are per-signature `Bool`
   facts about the chosen code (checker-computable over the
   declaration, same sense as the task's "no globals" example), not
   universals over syntax or runs — and the leaf frame is still derived
   from the fired step, never posited (rule 4a is respected: the
   conclusion's world/trace equations appear in no premise).
   `prog` deliberately stays general: the witness run `refB_prog` is a
   hand-built two-atom program (`take` + writing `leaf`), not an
   `Extraktion.progAus` image, so a `progAus` restriction would have
   made the required witness unstatable.
3. **Witness (rule 13).** `kette_aus_lauf_voll_zeuge` instantiates all
   premises jointly on `refB_pc_erreicht` (two steps by thread 1:
   `take`, then the writing leaf) with `code := fun _ => refEin`,
   proving `refO_gut`, the reachability, both rights facts (tables by
   case + `rfl`, globals vacuously over `Empty`), and the conclusion —
   plus non-degeneracy: `refEin` writes `konto`
   (`refEin_schreibt ()`) and memory moves (`refB_pc_schreibt`:
   slot `0 → 100`).

## Lean formatting lesson (for other lanes)

A multi-line term continuation whose indent does not pass the opening
bracket's column fails to parse (`unexpected identifier; expected '}'`
at the end of the first line). Measured: `refine ⟨{…` with the record
continued at 4–6 spaces fails; at 12–14 spaces it parses. Tactic
sequences and `rcases … | …` pattern continuations are unaffected.
`KetteVoll.lean` keeps `{…}` records shallow (continuation past the
bracket column) with single-line field proofs, and puts the long frame
proof in the top-level helper `kette_schritt_rahmen`.
