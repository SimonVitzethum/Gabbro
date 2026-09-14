# MUSE-REPORT-176 (lane 176, the stated obligation, 2026-09-14)

Task: a tool that states the user's obligation -- per function `KoerperGutS`
plus `InvGutS` over the lock-invariant family `S`, with the lock-invariant
establishment at the start memory, and a closing theorem deriving the
flagship's conclusion -- as `gabbro obligations <file.gab>`; refuse by name
everything `lean-g` refuses; prove 104's obligations once in
`grammatik/Grammatik/Pflicht104.lean`.

Branch `muse/176`. Rust + Lean lane. Last `./lean-bau` result line:
`Build completed successfully (182 jobs).` Last `./cargo-pruef`:
`== exit 0; failing tests: 0`. Last `./lean-probe` over both new files:
`== 0 error(s)` each.

## What was built

**`crates/gabbro-check/src/obligations_g.rs` (new).** Runs the `lean-g`
export and appends the obligation section: per function
`def <fn>_pflicht : Prop := KoerperGutS gP 0 (axWahr gD) gS g_<fn>` and
`def <fn>_invPflicht : Prop := InvGutS gP 0 (axWahr gD) gS g_<fn>` (defs,
sorry-free, no proofs -- the user's job), the families `pflicht`/
`pflichtInv`, `def startPflicht (sp : Speicher gD) : Prop` (the boot
duty), the decidable premises as named `by decide` theorems (`gP_voll`,
`gP_fragment`, `gP_fussS`), and `theorem gP_ziel` deriving the flagship's
conclusion from the obligations (open hypotheses) via
`ziel_ort_sperre_ende`. No refusal of its own: every `LG001`-`LG005`
travels untouched from `lean_g::export`. No new diagnostic code, no gift,
no example.

**`crates/gabbro-check/src/lean_g.rs`.** `namespace_of` made public,
`emit` takes the namespace as a parameter, new `export_ns` (export under
an explicit namespace) and `function_names` (the declared function names
in order, from the same `collect`). Plus one repair the probe forced
(see below): the emitted `RufPasst` proof is back to the checked
`hh_von`/`hx_von` shape, which holds for every emitted call by
construction (exact held sets, else `LG004`).

**`crates/gabbro-cli/src/main.rs`.** The new channel rides the existing
`obligations|pflichten` subcommand as `--g` (see below why not a new
subcommand name): checker errors refuse with `no export`, `LG` refusals
name the spelling that was typed, `--g` conflicts with `--isabelle`/
`--lean`. Help text extended. `crates/gabbro-check/src/lib.rs` registers
the module.

**`grammatik/Grammatik/GenOblig104.lean` (new, generated).** The tool's
output for `beispiele/104-referenz.gab` (namespace `G104_referenz_oblig`),
committed so the chain is checkable.

**`grammatik/Grammatik/Pflicht104.lean` (new, by hand).** Proves the stated
duties (`oblig_koerper` via `koerperGutS_ohne` over the `KoerperGutZ`
proofs adapted from `Schlusssatz104.lean` §4; `oblig_inv` via
`invGutS_leer`; `oblig_start` by cases; `oblig_hS` after `zS_ok`) and
applies `gP_ziel` once (`oblig_chain`). `grammatik/Grammatik.lean`
imports both files.

**`crates/gabbro-check/tests/obligations_g.rs` (new).** Pins the 104
output (both duties per function, families, boot duty, decided premises,
closing theorem, derived namespace, sorry-freedom, the export underneath)
plus one single-function snippet and the `LG001`/`LG004`/`LG005`
passthrough.

## Decisions, each with its reason

- **`--g`, not a new subcommand.** The name `obligations` is taken by the
  P6 register (`pflichten::zeige`), whose default output
  `miss-grammatikdeckung.py` parses (`obligation\t` lines). A second
  `obligations` subcommand cannot exist in one `match`; changing the
  default would break that instrument. The G-obligation channel is what
  `--isabelle`/`--lean` are to the P6 register: one more flag on the same
  subcommand. The lane's acceptance command reads
  `gabbro obligations --g beispiele/104-referenz.gab`.
- **Closing theorem is `ziel_ort_sperre_ende`, not
  `ziel_ort_mehrfaden_ende`.** The flagship's newest conclusion needs the
  per-thread call graphs (`AbgK`, `fussMehrB` over `lokK`) -- decidable
  only with thread-count and graph choices no tool can make mechanically.
  `ziel_ort_sperre_ende` has the same conclusion shape over the decidable
  footprint check (`fussSperreB`), i.e. exactly the premises a tool can
  discharge by `decide` plus the user's duties. Recorded here rather than
  hidden: upgrading the target is a lane of its own.
- **Obligation stated through the imported names, never copied.** The
  `def`s name `KoerperGutS`/`InvGutS` via `import Grammatik.ZielOrtStart`;
  no body text travels. The parallel `passes`-quantification rework can
  move those bodies without aging a single stated duty (only the applied
  arguments `gP 0 (axWahr gD) gS` could need a touch, loudly, at
  elaboration).
- **`SperrInvOk gS` stays a hypothesis of `gP_ziel`.** Its second half
  quantifies over memories (functions) and is not decidable in general;
  discharging it in the file would be a proof, i.e. the user's job. For
  104 `Pflicht104.lean` proves it (`oblig_hS`).
- **`StartExklusiv` stays a hypothesis of the 104 chain.** Every function
  of `gD` holds `M` by signature, so no start assignment of `gP` alone is
  exclusive (the `gP_kein_exklusiv` finding, `Schlusssatz104.lean` §5).
  `oblig_chain` closes everything else (hardware by construction, decidable
  premises by `decide`, both duties proved) and names the one fact no `gP`
  program can supply. The runtime's idle root is that file's §5, unchanged.

## Verification -- all green, measured 2026-09-14

- `./cargo-pruef`: `== exit 0; failing tests: 0` (includes the new
  `obligations_g` target and the `fahnen` register test).
- `gabbro obligations --g beispiele/104-referenz.gab`, diffed against
  `grammatik/Grammatik/GenOblig104.lean`: **byte-identical**.
- `./lean-probe grammatik/Grammatik/GenOblig104.lean`:
  `== 0 error(s)`, exit 0.
- `./lean-probe grammatik/Grammatik/Pflicht104.lean`:
  `== 0 error(s)`, exit 0; `oblig_koerper`, `oblig_inv`, `oblig_chain`
  depend on axioms `[propext, Classical.choice, Quot.sound]` only.
- `./lean-bau`: `Build completed successfully (182 jobs)`, 0 error lines
  (both new files joined the build through `Grammatik.lean`).
- `./emission-pruef` not run: the C emitter (`emit.rs`) is untouched; the
  only emission-side change is the `lean-g` `RufPasst` proof shape below,
  which ships no C.

Two probe findings on the way there, both fixed and re-measured:

1. The `lean-g` `gHp` proof shape (`hh := fun L => ...`, no `hx`) does
   not check -- the paste in `Export104.lean` still carries the proven
   `hh_von`/`hx_von` form, and no fresh `lean-g` output had been probed
   since the change. The emitter now writes the proven form again
   (`hh := RufPasst.hh_von ...`, `hx := RufPasst.hx_von ...`), which is
   correct for every emitted call by construction (the exporter only
   emits exact held-set calls, else `LG004`). `Export104.lean` is
   verbatim-accurate again.
2. `(axEnsLokal_wahr _)` is an application error -- the lemma takes no
   explicit argument (witnesses pass it bare). The closing theorem now
   passes `axEnsLokal_wahr`.

## Files

- `crates/gabbro-check/src/obligations_g.rs` (new)
- `crates/gabbro-check/src/lean_g.rs` (export_ns, function_names, pub
  namespace_of, namespaced emit)
- `crates/gabbro-check/src/lib.rs` (module registration)
- `crates/gabbro-cli/src/main.rs` (`--g` on `obligations|pflichten`,
  help text)
- `crates/gabbro-check/tests/obligations_g.rs` (new)
- `grammatik/Grammatik/GenOblig104.lean` (new, generated output for 104)
- `grammatik/Grammatik/Pflicht104.lean` (new, the user's half for 104)
- `grammatik/Grammatik.lean` (two imports)
