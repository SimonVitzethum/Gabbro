# MUSE-REPORT-1173: Profiles — hosted OS and freestanding entry/ABI/image

## What was done

NEW FILE `grammatik/Grammatik/X86/PipelineProfiles.lean` (~455 lines),
plus one `import Grammatik.X86.PipelineProfiles` line appended to
`grammatik/Grammatik.lean`. No existing file was otherwise touched;
`OptimizationRules.lean`/`OptimizationWitnesses.lean` untouched.

Checked profiles (no implicit Linux/POSIX/libc/ELF): a `ZielProfil`
(`gehostet` | `frei`) with, per profile, the entry kind
(`profilEintritt`: `hostedMain` / `nolibcMain`, IMAGE-ABI sec. 5), the
stated integer parameter ABI (`profilAbi`: System V order as data, so a
future target varies it without forking the validator), the checked
entry sequence (`profilProlog` = accepted `PipelineEntry.prolog` at the
profile ABI, with its run `profilProlog_lauf` reusing `zuege_lauf`), and
the one checked admission `profilOk` (hooked entry AND support).

Every selected profile keeps complete final-byte, entry, support-code
and mapping validation: admission implies the executable RIP through
the CHECKED loaded mapping, the entry stack window, and every support
half (image bytes with decode coverage, gate, arena layout, stub
bindings, trap suffix, float control word); `stuetzSchritt` forces
canonically loaded image memory so all reachable support bytes are
covered or refused (`profilOk_stuetz_schritt` /
`profilOk_stuetz_verweigert`). Environment services are user logic;
only hardware behaviour is assumed.

## Exact names of new definitions/theorems

Defs: `ZielProfil`, `profilEintritt`, `profilAbi`, `profilOk`,
`profilProlog`.
Theorems: `profilOk_teile`, `profilOk_eintrittZulassung`,
`profilOk_eintritt`, `profilOk_haken`, `profilOk_status`,
`profilOk_folgen`, `profilOk_erster_schritt`, `profilOk_stuetz_schritt`,
`profilOk_stuetz_verweigert`, `profil_verweigert_ohne_anfang`,
`profil_verweigert_ohne_ende`, `profil_verweigert_status`,
`profil_verweigert_unlisted`, `profil_verweigert_tor`,
`profil_verweigert_ohne_bild`, `profil_verweigert_ohne_mxcsr`,
`profilProlog_gerade`, `profilProlog_lauf`,
`pipeline_profil_verbindung`, `profil_gehostet_ok`, `profil_frei_ok`,
`pipeline_profil_verbindung_zeuge`.

## Last `./lean-bau` result line

`Build completed successfully (608 jobs).`

`./lean-probe` on the new file: `0 error(s)`. `#print axioms` for every
main theorem: only `propext` and (via reused producer lemmas)
`Quot.sound` — subset of the standard goal axioms, no new axiom, no
`sorry`/`admit`/`native_decide`/`unsafe`.

## What remains open

See the `CUTS` block at the end of the file: no source correspondence
(waits on lane 287 IR), no hardware/silicon correspondence, no TSO/W/GX
bridge, no budget/cost transfer, no multi-step control-flow or
relocation re-decoding, no kernel behaviour beyond the named
assumption. `verweigert` is absence of a transition, not termination.

## `_zeuge` (non-degenerate)

`pipeline_profil_verbindung_zeuge` instantiates BOTH profiles jointly on
the minimal image (`valZeuge`, both hooks, unchanged zero status) with
the fetched `ret` and its executed step (`zulassung_fetch_ret`,
`zulassung_schritt_ret`), a real memory-changing write/read
(`schreibLese_zeuge`), a table some function writes
(`zeugenU_schreibt`: `setze` writes `konto`), and four planted
refusals (missing `anfang`, changed status, W^X image, clobbered gate).

## Anything in the task believed wrong

Nothing. One remark: the task lists `ComposeProfileSelect.lean` among
the profile sources; its selector (`waehleNull` zeroing choice,
`fallback` feature choice) is a CPU-tuning composition, not an OS
profile, so this file reuses the entry/support producer interfaces
instead and leaves CPU feature selection with lane 844. No premise was
added, no conclusion weakened.

## Repair after failed integration gate (no merge happened)

Integration evidence: `exit 1; 2 error line(s)` with
`[609/610] Building Grammatik` failing as
`lean -j2 -M4096 ... Grammatik.lean` aborting with
`libc++abi: ... failed to create thread`, exit 134. The log prints all
of this module's `#print axioms` lines (448-454) BEFORE the failure, so
`PipelineProfiles.lean` itself elaborated and built; no error line
points at any owned file. This is the documented apparatus resource
failure (thread-spawn/virtual-address exhaustion at the aggregate
target), not a Lean error in owned code.

Repair: NO semantic change. Nothing was weakened, no premise added, no
conclusion touched — there is no defect in the owned module to repair,
and weakening a guarantee to make a gate green is forbidden. Verified
instead: the import line stands exactly once at the end of
`grammatik/Grammatik.lean`; the owned file contains no `sorry`,
`admit`, `axiom`, `native_decide` or `unsafe` (only the English words
"admitted"/"REFUSAL" in doc comments); axioms unchanged (`propext`,
`Quot.sound` via reused producer lemmas only).

Fresh local checks after the failure: `./lean-probe`
`grammatik/Grammatik/X86/PipelineProfiles.lean` gives
`0 error(s)`; `./lean-bau` gives
`Build completed successfully (608 jobs)`, including the aggregate
`Grammatik` target that failed at integration. Full source-to-binary
chain acceptance is NOT claimed. A fresh independent review of the
changed commit is still required.
