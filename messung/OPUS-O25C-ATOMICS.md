# Opus lane O25c — the atomic rely IS the goal theorem

*2026-09-26. Worktree branch `worktree-agent-a2504cb87a2b94e0a`, merged with master at
`1800a7a3` (Opus G `folge`, lane 267, Opus H handlers). SATZKARTE §57; OFFEN O25 (narrowed to
the payload rule), O17; TODO §2; AGENTS §2/§7. Everything built and tested locally through the
queued wrappers.*

## 1. Verdict

**The ONE Spec diff is made.** `GabbroZiel` is now the statement with the atomic rely, proved
(`gabbro_ziel`, `Zielsatz/BeweisAtomar.lean`), and the statement of before is kept verbatim as
`GabbroZielSC` and DERIVED from it (`gabbro_ziel_sc_aus`). No leg of before is lost: every leg
`GabbroZiel` had (including Opus G's `folge` and Opus H's contentful `keinKernHalt`) is a leg of
the new conclusion, over the same or more runs. Same for linked units (`GabbroZielVerbund`,
`gabbro_ziel_verbund_sc_aus`).

`#print axioms` (`grammatik/NachpruefungZiel.lean`, after the final build): `gabbro_ziel`,
`gabbro_ziel_sc`, `gabbro_ziel_sc_aus`, `gabbro_ziel_verbund`, `gabbro_ziel_verbund_sc_aus` --
each exactly `[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, `axiom`,
`native_decide` in any new or changed file.

## 2. The Spec diff, reviewed

**Premises, before → after:**

| group | before (`GabbroZielSC`) | after (`GabbroZiel`) | direction |
|---|---|---|---|
| (a) | `C : Pruefer`, sound against `AkzeptiertSpec` | `C : PrueferX`, sound against `AkzeptiertSpecX`: `fuss := FussSX` over `GeteiltV P ws` (an `atomic`, unguarded, not thread-local, in no contract), every other field (incl. Opus H's `masken`) identical | relaxation: `Pruefer.alsX` (via `akzeptiertSpecX_of_spec`) keeps every checker and verdict |
| (b) | `NutzerPflicht E` | `NutzerPflichtA E`: bodies against every value a read of a shared atomic (`GeteiltA E.P E.ws`) may return | strengthening only where another thread interferes (`hP_rely_nicht`); EQUIVALENT on every unit the old checker accepts (`logikPflichtA_iff_akzeptiert`) |
| (c), (d) | unchanged | unchanged | — |

**Conclusion, before → after:** `ZielF` on every `FadenErreichbar` (thread machine over G) →
`ZielFX` on every `FadenErreichbarX` (thread machine over GX: G whose reads of `GeteiltV E.P E.ws`
the weak memory answers). Leg by leg (`ZielX`):
- same statement at every GX-reachable machine: `speicherSicher`, `vertrag`, `sperrInv`,
  `invRueck`, `invGrund`, `invRuhe`, `invSicht`, `startEnde`, `keinStartGrund`, `keinLogikHalt`,
  `keineVerklemmung`, `keinZyklus`, `fortschritt`, `folge`; thread legs `schlafendUnberuehrt`,
  `schlafendFrei`, `joinFrei`, `keineVerklemmung`, `keinZyklus`;
- over more runs/steps: `rennfrei` (`RennfreiBisGA`), `sperrWechsel`/`sperrSicht` (GX steps),
  `keinKernHalt` (`KernHaltEA`: Opus H's leg over GA runs), `zeit` (`ZeitAbX`: GX segments),
  thread `fortschritt`/`spawnSicht` (GX thread steps);
- changed form: `schwach` = `SchwachX` (every W step is a GX step and presents G's memory
  outside the shared atomics). `SchwachSC` is false on an accepted flag program
  (`n1_schwachSC_falsch`); with no shared atomic the forms coincide.

**Embedding (old statement derivable):** `gabbro_ziel_sc_aus : GabbroZiel → GabbroZielSC` --
`Pruefer.alsX`, `nutzerPflichtA_of_akzeptiert` (old checker + old (b) give the new (b)),
`fadenErreichbarX_of` (every G thread run is a GX one), `geteiltV_leer` (a unit the old checker
accepts has NO admitted shared atomic), `zielF_of_X` (with no shared atomic `ZielFX` is `ZielF`;
`gx_leer_g`: GX over an empty set is G; `kernHaltE_of_EA`, `rennfreiBis_of_GA`, time via
`SegLauf.alsX`). `gabbro_ziel_sc` is also still proved directly (`Zielsatz/Beweis.lean`).

**Header:** the atomic-rely block (gap, diff, RMW, why nothing is weakened, what carries the
proof, witnesses, what stays named); SHAPE paragraph; WHAT A GREEN BUILD COVERS (certificates
now decide `akzeptiertX_pruefer`, state `ZielFX`/`ZielX`; counts 204 accepted / 25 CERTIFIED /
179 UNCERTIFIED); reading assumption (2) now names the RMW lowering; NOT CLAIMED: the O25 line
REPLACED (now named: contracts over a shared atomic, per-core merge discipline, atomics shared
across a link); the plain-payload hand-off line kept; Opus G's O29 lines untouched; Opus H's
remark on `ZielAtomar` completed.

## 3. The pieces (task items)

| # | item | status | where |
|---|---|---|---|
| 1 | thread machine and `GabbroZielVerbund` with the rely | DONE | `Speichermodell/GXMaschine.lean` (`FadenSchrittX`, `FadenInvX`, `SegLaufX`, `frame_schritte_beschraenktX`, `gx_leer_g`), `Zielsatz/BeweisAtomar.lean` (`zielX_aus`, `zielFX_aus`, `keine_verklemmungFX`, `folgeG_erreichbarX`, `kernHaltEA_aus`, `akzeptiertSpec_verbindeX`, `gabbro_ziel_verbund`) |
| 2 | RMW atomicity in `SchrittW` | DONE | field `SchrittW.rmw` (`MaschineW.lean`; `ExchangeKopf` moved there), `w_kein_verlust`, `wr_iff` (`RMW.lean`); witnesses re-proved (`w_nicht_sc` shows its step has no exchange head) |
| 2 | the counter ending at 2 on W | PARTLY | `Speichermodell/ZaehlerW.lean`: `w_kette`, `w_zaehler`, `w_zaehler_zwei` -- on EVERY W run, if every write of the atomic is an `exchange` adding one (`ZaehltHoch`, a hypothesis), the history is the gap-free chain and the newest message is start + number of writes. NOT done: a concrete program term discharging `ZaehltHoch` (a rule inversion per step, as `g_schritt_0`) |
| 3 | plain payload after `awaits` (N485, gifts 1205–1210) | NOT DONE | see §5 |
| 4 | the ONE Spec diff | DONE | §2 |
| 5 | exporter for `atomic` items | DONE for the payload-free class | `lean_g.rs` `read_atomic` (payload, `observed by`, non-scalar, zero outside the range refused by name), `Stmt.publish … []` for `publishes nothing`, `atomar := …`; `obligations_g.rs` emits certificates over the new statement; `beispiele/116` and new `beispiele/162-geteilte-flagge.gab` CERTIFIED (162 refused by the old checker: `g162_alt_abgelehnt`) |
| 6 | docs | DONE | SATZKARTE §57, OFFEN O25/O17, TODO, AGENTS §2/§7 |

**Witnesses (non-degenerate):** `n1E_gabbro` (`gabbro_ziel` on the flag program, refused by
the old checker); `n1_stale_x`, `n1_gx_nicht_g` (W's stale read is a GX step over the admitted
shared atomics, NOT a G step, and `ZielX` holds after it); `g162_*` (a certified shared-atomic
program); `hP_rely_nicht`, `vertrag_atomar_abgelehnt`, `faltung_akzeptiertX` (lane O25b).

## 4. Measurements

* `./lean-bau` (final, after merging master `1800a7a3`): exit 0, 0 error lines.
* `./cargo-pruef` (final): exit 0, **1402 passed, 0 failed, 1 ignored**.
* `GABBRO_ZERTIFIKATE=schreiben cargo test --test zertifikate` (through the lock): register
  `204 accepted, 25 CERTIFIED, 179 UNCERTIFIED` (before: 203 / 23 / 180; +116, +162).
* `pruefe-todo.py`: 16 findings (the same stale EBNF/count findings as the base, not this lane's);
  `pruefe-kennungen.py`: ALL PASS.
* `free -g` during the work: 31 GB total, 13–21 GB available (local machine).

## 5. What remains (exactly)

1. **The plain-payload rule (OFFEN O25 remainder; `N485`, gifts 1205–1210 reserved, unused).**
   Admitting a PLAIN carrier read after an `awaits` of a release-published flag needs (i) the
   leg `rennfrei` in a form "ordered by a lock OR by a release/acquire hand-off" (today a
   cross-thread write/read pair must be lock-ordered), (ii) flow facts in the checker and in
   Lean (the producer writes the payload only before its `publishes`, the consumer reads it only
   after its `awaits`), (iii) the replay seeing the payload stable across the hand-off; the
   memory part is `hb_uebergabe`. A second Spec diff; not started, so no Rust code was minted.
2. The counter's program side: a concrete two-thread `exchange` term shown to meet `ZaehltHoch`.
3. The exporter for payloads, `awaits`, `exchange`, atomic arrays and `accumulates` (still
   `LG001`/`LG002`/`LG004` by name); the certificate header lists an atomic as `static N` (cosmetic).
4. Linked units sharing an atomic across the link (the link check's `lok` is unchanged, so such
   links are refused and named in NOT CLAIMED).

## 6. Files

Lean new: `Speichermodell/{GXMaschine,ZaehlerW}.lean`, `Zielsatz/{BeweisAtomar,AtomarGoalZeuge,
AtomarZertifikatZeuge}.lean`, `Zertifikat/{G116_payload_free_counter,G162_geteilte_flagge}.lean`.
Lean changed: `Zielsatz/Spec.lean` (the diff), `Speichermodell/{MaschineW,RMW,Zeuge}.lean`,
`Zielsatz/{Beweis,Verbund,VerbundZeuge,FaedenZeuge,Schwach,FolgeZiel,AtomarPflicht,
AtomarAkzeptiert,AtomarZiel,AtomarInvarianten,AtomarMasken}.lean` (renames `gabbro_ziel` →
`gabbro_ziel_sc` for the statement of before; definitions moved into Spec), `Pflicht104/108.lean`,
all certificates (regenerated), `NachpruefungZiel.lean`, `Nachpruefung.lean`.
Rust: `lean_g.rs`, `obligations_g.rs`, `tests/{lean_g,obligations_g,zertifikate}.rs`.
Corpus: `beispiele/162-geteilte-flagge.gab`.
