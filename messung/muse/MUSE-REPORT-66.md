# MUSE-REPORT-66: one hardware profile -- Lean model (E6, model half)

Lane 66, branch `muse/66`. New file `grammatik/Grammatik/Profil.lean` (626 lines);
`grammatik/Grammatik.lean` gains `import Grammatik.Profil`. No other files touched.
No Rust changes, so no `./cargo-pruef` / `./emission-pruef` runs.

## What I did

Built the E6 model half per `PLAN-ERWEITUNG.md` section 0c:

- `ProfilSchluessel`: finite inductive with `fpRundung`, `fpKontraktion`,
  `speichermodell`, `arch`, `interruptRouting` (`DecidableEq`).
- `AnnahmeEintrag D`: `.modus name klasse key val` or `.frei name klasse claim`
  where `claim : World D -> Prop` is stored as a structure field (never a
  theorem premise, per the task).
- `Profil D := List (AnnahmeEintrag D)`; `ModusBelegung := ProfilSchluessel -> Nat`.
- `Profil.gut P := einigung P /\ (same-name content agreement)`, where
  `einigung` is key agreement and `namensGleichheit` compares full content
  (keyed: class/key/value; free: class plus prose `iff` at one witness world).
- Decidable for keyed entries: `pruefeSchluessel : Profil D -> Bool`
  (pairwise `schluesselKonflikt` check) with correctness
  `pruefeSchluessel_einigung : pruefeSchluessel P = true -> einigung P`.
- `Bibliothek D`: name plus `anforderungen : List (Anforderung D)`;
  `Profil.bindet P lib`: every requirement is in the profile by NAME with
  identical content.
- Theorems: `profil_modell` (a `gut` keyed profile induces a satisfying mode
  via `modusVonProfil`), `bindung_fuegt_nichts_hinzu` (binding implies the
  library's conjunction from the profile's -- via `namensGleichheit_erfuellt_modus`),
  `widerspruch_abgelehnt` (same key, different values refutes `gut`).
- Witness: `zeugeD` (one `bool` table, writer signature, following
  `BlattGegenbeispiel.D1`), `zeugeProfil` (arch = 1, fpKontraktion = 0),
  `zeugeBibliothek` (requires fpKontraktion = aus), with `zeugeProfil_gut`,
  `zeugeProfil_keyed`, `zeugeBibliothek_bindet`, and the joint witnesses
  `profil_modell_zeuge`, `bindung_fuegt_nichts_hinzu_zeuge`.

## Exact names of new definitions/theorems

Defs: `ProfilSchluessel`, `AnnahmeEintrag`, `Profil`, `ModusBelegung`,
`eintragName`, `istModus`, `modusVonProfilAux`, `modusVonProfil`, `eintragWert`,
`einigung`, `namensGleichheitAux`, `namensGleichheit`, `Profil.gut`, `erfuellt`,
`Profil.gilt`, `schluesselKonflikt`, `pruefeSchluesselAux`, `pruefeSchluessel`,
`Anforderung`, `anforderungEintrag`, `Bibliothek`, `anforderungName`,
`profilEintrag`, `Profil.bindet`, `Bibliothek.gilt`, `zeugeArch`,
`zeugeKontraktionAus`, `zeugeD`, `zeugeProfil`, `zeugeBibliothek`.
Theorems: `modusVonProfil_kopf`, `eintragWert_trifft`, `istModus_inj`,
`modusVonProfil_trifft`, `pruefeSchluesselAux_kons`, `keinKonflikt_einigung`,
`pruefeSchluessel_einigung`, `namensGleichheit_erfuellt_modus`,
`bindung_fuegt_nichts_hinzu`, `widerspruch_abgelehnt`, `profil_modell`,
`zeugeProfil_gut`, `zeugeProfil_keyed`, `zeugeBibliothek_bindet`,
`profil_modell_zeuge`, `bindung_fuegt_nichts_hinzu_zeuge`.

## Last `./lean-bau` result line

`Build completed successfully (37 jobs).` -- first line:
`== 0 error line(s) in the COMPLETE output`.
`#print axioms` for all five main theorems: `[propext, Classical.choice, Quot.sound]`
(standard Lean, no `sorry`/`axiom`).

## What remains open

- No `pruefeName` boolean: same-name content over prose `Prop`s is not
  computable; the name half of `gut` is stated, not decided (booked in CUTS).
- No wiring into a program theorem: no goal theorem takes the profile yet.
- Free-prose entries carry no falsifier probe bookkeeping.
- `sucheModus` (the `find?`-based lookup) was dropped in favor of
  `modusVonProfil` (structural recursion): the `find?` property lemmas needed
  do not exist under these names in Lean 4.33.1, and the projection proves the
  same read-back (`modusVonProfil_trifft`) without them.

## What I believe is wrong in the task

- Rule 13 demands the witness program have "a reached run with at least one
  step that changes memory" for run statements. This lane's theorems are about
  profiles and libraries, not runs -- there is no `Stmt`/`PCReach` premise to
  witness. I provide the next best thing the rule allows: a non-degenerate
  declaration (`zeugeD` has a table with a writer signature). A run witness
  would be vacuous here since no theorem mentions a run; adding one would be
  decoration, not evidence. If the gate insists on a run, that is a finding
  about the gate, not the theorems.
- The task's `bindung_fuegt_nichts_hinzu` ("the conjunction of requirements is
  implied by the profile's conjunction") is stated over mode assignments
  (`Bibliothek.gilt`/`Profil.gilt`), which only constrain keyed entries; free
  prose is carried by name-identity, not implication. The proved form is the
  honest reading: linking adds no *mode* premise.
