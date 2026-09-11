# PORT-MASCHINE — port audit: `Maschine.lean` from `wip/maschine-pflicht-2026-09-11` against master `58d6b83`

- Subject: `grammatik/Grammatik/Maschine.lean` at `85cb4f4` (1653 lines: W1/W2/W4
  derivations, every-carrier-guarded core).
- Base: master `58d6b83` (lane-110 worktree, clean).
- Method: read-only. No `lake`/`cargo` run, no elaboration executed. Claims below rest on
  `git show`/`git diff`/`grep` evidence with `file:line` citations, plus the WIP commit's own
  measurement record. Line numbers prefixed `M:` refer to the WIP `Maschine.lean`
  (`M:27` = line 27); all other `file:line` citations name their file and revision.

## 1. Does it elaborate standalone?

**YES in its own tree, NO against master.**

- In-tree: the file contains zero `sorry`, `admit`, or `axiom` (grep over all 1653 lines:
  no hits; the only `#print axioms` is `M:1651`, a report, not an assumption). The WIP
  commit message (`85cb4f4`) records `lake build` green — at 11 theories, because the WIP
  `Grammatik.lean` index drops 17 theories (see §4). That measurement is quoted, not
  re-run here.
- Against master `58d6b83`: it does not elaborate. Five breakage points, B1–B5 (§3). The
  `import Grammatik.Wettlauf` (`M:27`) itself still resolves on master — the failures are
  use sites, not the import.

## 2. What it assumes (premises, read off the signatures)

Explicit hypotheses threading the top theorems (`schritt_gut` `M:1275`,
`maschine_schritt_gut` `M:1502`, `erreichbar_gesittet` `M:1577`, `faeden_gesittet` `M:1645`):

| # | Premise | Where |
|---|---------|-------|
| P1 | `GutO O` — the oracle answers inside its declared type | `M:690`, `M:753`, `M:1498`, `M:1645` |
| P2 | `Fremd Ms` — ownership marks are pairwise disjoint across threads (`M:1337`) | `M:1467`, `M:1577`, `M:1647` |
| P3 | `MaschineGut M0 Ms` — the four-part machine invariant G1–G4 (`M:1340`) | `M:1577` |
| P4 | No thread starts holding a lock: `∀ p ∈ fs, (D.signatur p.1).haelt = []` | `M:1604–1605`, `M:1646` |

Declaration fields assumed beyond what master provides:

| # | Field | Status on master |
|---|-------|------------------|
| P5 | `D.invarianten_marken` (used `M:486`) | MISSING — master `Syntax.lean:181` has only `invarianten_gehalten`; added by WIP `Syntax.lean:185` |
| P6 | `D.eigner` / `D.eigner_nie_erzeugt` (used `M:416`, `M:438`, `M:462`) | present — master `Syntax.lean:144`, `Syntax.lean:149` |
| P7 | `D.konsumiert` (used `M:1591`) | present on master |
| P8 | 4-tuple `Brav` with `∃ neu, σ'.spur = neu ++ σ.spur` (used `M:648`) | MISSING — master `Satz.lean:258–259` is a 3-tuple; 4th component added by the WIP `Satz.lean` diff |
| P9 | 4-field `Gesittet` without `ungeteilt`, `marke_eindeutig` with leading `∃ t, m ∈ D.eigner t` premise (built `M:1467–1495`) | MISSING — master `Wettlauf.lean:181–195` has 5 fields including `ungeteilt` and the premise-free `marke_eindeutig`; reshaped by the WIP `Wettlauf.lean` diff |

Logic footprint (inferred, not built): `Classical.byContradiction` at `M:1494`, so the
`#print axioms Gabbro.Grammatik.faeden_gesittet` at `M:1651` reports at least
`Classical.choice` (plus the standard `propext`/quotient closure). No other classical use
in the file.

## 3. Breakage list against master `58d6b83` (all five are errors, not drift)

- **B1 — unknown constructor.** `Stmt.eigner_mono`, `M:494–497`: the match arm
  `| .behauptung .., _, h` names `Stmt.behauptung`, which exists only in WIP
  `Syntax.lean:432` (`assert n: p` / `lemma n: p`). Master `Syntax.lean` has no such
  constructor.
- **B2 — unknown declaration field.** `eigner_invSicht`, `M:486`:
  `D.invarianten_marken (D.sig f) i hi t ht m s hb`. Master `Syntax.lean:181` provides only
  `invarianten_gehalten`; `invarianten_marken` is WIP `Syntax.lean:185`.
- **B3 — unknown constructor + missing equation.** `blatt_neu`, `M:716–720`: the
  `| .behauptung n c` arm needs `Stmt.behauptung` (missing, see B1) and an `execStmt`
  equation for it (master `Semantik.lean` has none; WIP adds the equation near WIP
  `Semantik.lean:582–590` together with `Logik.behauptung` at WIP `Semantik.lean:297`,
  likewise absent on master).
- **B4 — ill-typed projection.** `weltGut_brav`, `M:645–659`, specifically `hb.2.2.1` at
  `M:648`. Master `Brav` (`Satz.lean:258–259`) is a 3-tuple, so `.2.2` is the
  `Konsistent`-preservation implication and `.2.2.1` does not exist. The projection is
  well-typed only against the WIP 4-tuple `Brav` (4th component `∃ neu, …`, WIP `Satz.lean`
  diff hunk 1, with `Brav.refl`/`Brav.trans`/`gut_merke`/`gut_schreibSlot`/`gut_schreibGlob`/
  `gut_nimmt_gibt`/`axiomAntwort_gut` adjusted for it).
- **B5 — constructor arity + argument mismatch (two errors in one theorem).**
  `gesittet_von`, `M:1467–1495`: the anonymous constructor at `M:1469`
  `⟨?_, ?_, hM.ausschluss, ?_⟩` supplies 4 fields, but master `Gesittet`
  (`Wettlauf.lean:181–195`) takes 5 (the 5th is `ungeteilt`, deleted in the WIP diff);
  and the final component at `M:1493–1495` passes an extra leading argument
  `he : ∃ t, m ∈ D.eigner t` to `marke_eindeutig`, whose master signature
  (`Wettlauf.lean:189–191`) takes no such premise (added in the WIP diff).

## 4. Verdict per section

Sections are the file's own `/-! ## … -/` divisions.

| Section | Lines | Verdict | Reason |
|---------|-------|---------|--------|
| §1 Speicher, Ergebnisse | `M:33–96` | MERGEABLE-YES | Uses only `World`/`Env`/`Ausgang`/`ErgVal`/`Logik`/`Hardware` names unchanged on master. |
| §2 Fortsetzungen, Fäden | `M:97–148` | MERGEABLE-YES | `RufArt`/`Kont`/`Aktiv`/`Zustand` reference only shared `Block`/`Endblock`/`D.gruende`/`D.erg` shapes. |
| §3 Fadenschritt | `M:149–410` | MERGEABLE-YES | `starteStmt`/`starteBlock`/`starteEnde`/`rufStart`/`rufEnde`/`verbrauche`/`schritt` name no WIP-only declaration; the catch-all delegates new forms to `execStmt` generically. Behaviour differs on master (no `.behauptung` equation), but the code as written references nothing missing. |
| §4 Fadeninvariante | `M:412–573` | MERGEABLE-NO | B1 (`M:496–497`), B2 (`M:486`). |
| §5 Schritt erhält Invariante | `M:575–1291` | MERGEABLE-NO | B3 (`M:716–720`), B4 (`M:648`). |
| §6 Scheduler | `M:1293–1328` | MERGEABLE-YES | Pure `List`/`Nat`/`Bool` code over the local `schritt`; no core names beyond `Lauf`/`Zustand`/`Ereignis`. |
| §7 Maschineninvariante, gesittet | `M:1330–1581` | MERGEABLE-NO | B5 (`M:1467–1495`). The surrounding lemmas (`MaschineGut`, `Lauf.spur_*`, `maschine_schritt_gut`, `erreichbar_gut`, `erreichbar_gesittet`) are portable on their own. |
| §8 Anfang, Fäden starten | `M:1583–1653` | MERGEABLE-YES (code) | `Faden.start`/`Anfangsmarken`/`Maschine.start`/`Startmarken`/`start_gut` use only shared names (`D.konsumiert`, `Signatur.anfang`, `held_anfang`, `Lauf.spur_zero`, `konsistent_nil` — all on master). Note: `faeden_gesittet` (`M:1645`) calls `erreichbar_gesittet` from NO-section §7, so the top theorem is not portable even though §8's own code is. |

**File verdict: MERGEABLE-NO.** The portable sections (§1–§3, §6, §8) cannot be taken as a
file because §4, §5, §7 fail against master, and the file's crown theorem
(`faeden_gesittet`, `M:1645`: started threads, interleaved, are `Gesittet`, hence
`kein_wettlauf` applies) depends on all three failing sections.

## 5. Checked non-issues (looks breaking, is not)

- **B26 rename (`Logik.vorzustand` → `Logik.uebergang`).** `Maschine.lean` never names either
  constructor (only `Stmt.uebergang`, whose name is unchanged, at `M:496`, `M:721`). The
  rename (master `Semantik.lean:281–284` vs WIP `Semantik.lean:295`) affects `Pflicht.lean`
  and proofs about `execStmt` outcomes, not this file's references.
- **`World`/`Ereignis`/`Orakel` API.** Unchanged between the revisions (the WIP `Semantik.lean`
  diff touches only `Expr.orte`, `bereich`, `eval`, `Logik`, `execStmt`). `Speicher.welt`
  (`M:40`), `σ.nimmt`/`σ.gibt` (`M:236`, `M:370`), `O.regLies`/`O.sichtbar`/`einpassen`/
  `D.rzusage` (`M:269–290`) all resolve on master.
- **Helpers used by portable sections.** `konsistent_tail` (master `Wettlauf.lean:84`),
  `Lauf.spur_zero` (master `Wettlauf.lean:62`), `held_anfang` (master `Satz.lean:731`),
  `konsistent_nil` (master `Satz.lean:246`), `D.eigner`/`D.eigner_nie_erzeugt` (master
  `Syntax.lean:144`/`149`) exist identically on both sides.
- **The 17 dropped theories** (`Ziel`, `Interferenz`, `Koernung`, `Geteilt`, `Geraet`,
  `Unterbrechung`, `Zeugnis`, `Budget`, `Terminierung`, `InterferenzAllgemein`,
  `Komposition`, `Fehler`, `Erhaltung`, `Extraktion`, `Marken`, `Fristlauf`, `Adressraum` —
  removed from the WIP `Grammatik.lean` index) do not affect this file: it imports only
  `Grammatik.Wettlauf` (`M:27`).
- **Staleness context, quoted from `85cb4f4`.** The WIP was written against the 2026-09-09
  night state: its `Wettlauf.lean` is 12+/20- away from `52837ae` but 12+/198- away from
  `be49250`; it reverses B26 and drops `SYNTAX.md` §§19–21 plus the 2026-09-10/11 rows.
  That is why a file-level merge is out of scope — this audit only scores `Maschine.lean`.

## 6. Port path (consequence, not a plan)

A port takes the YES-sections (§1–§3, §6, §8) nearly verbatim, then chooses per NO-section:
§4 needs either `Stmt.behauptung` + `D.invarianten_marken` carried onto master (core change)
or the two arms Lemmas re-proved without them; §5 needs the 4-tuple `Brav` (core change,
touches every `Brav`/`Gut` constructor proof in `Satz.lean`) or a `weltGut_brav` that does
not project `.2.2.1`; §7 needs `Gesittet` without `ungeteilt` (deletes master W5, touches
`Ziel.lean`/`Interferenz.lean` consumers) or a `gesittet_von` that also discharges
`ungeteilt`. Either direction is a core change, not a fast-forward — consistent with the
WIP commit's own integration note.
