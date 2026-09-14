# MUSE-REPORT-169: Isabelle to Lean port (8 theories)

Lane 169. Machine: `ki-pc-fisch-101` (hostname `fisch`, 110 GB RAM).
Toolchain: `leanprover/lean4:v4.33.1`, no mathlib, no `programmlogik`/`passlogik`
imports. Full build: `lake build` in `grammatik/` --
**Build completed successfully (162 jobs).**

## What was delivered

Eight new files under `grammatik/Grammatik/Isabelle/`, one per theory, all
imported at the end of `grammatik/Grammatik.lean`. `beweise/` was not touched
(`git diff --stat -- beweise/` is empty). No `sorry`, no `axiom` declarations,
no `native_decide` in any new file (verified by clean build plus `#print axioms`
at the end of each file; zero `sorryAx`).

Verification with the repo's own scripts (2026-09-14, on `ki-pc-fisch-101`):
`./lean-bau` -- exit 0, 0 errors, "Build completed successfully (162 jobs)";
`./cargo-pruef` -- exit 0, 0 failing tests (Rust untouched by this lane, checked
anyway). `./emission-pruef` not applicable (emitter untouched).

| # | Isabelle theory | Lean file | Isar lines |
|---|---|---|---|
| 1 | `Accumulates_Monoid.thy` | `Isabelle/AccumulatesMonoid.lean` | 235 |
| 2 | `Gruppe_Erhaltung.thy` | `Isabelle/GruppeErhaltung.lean` | 242 |
| 3 | `Format_Roundtrip.thy` | `Isabelle/FormatRoundtrip.lean` | 180 |
| 4 | `Option_Sonderwert.thy` | `Isabelle/OptionSonderwert.lean` | 168 |
| 5 | `Consuming.thy` | `Isabelle/Consuming.lean` | 167 |
| 6 | `Device_Konstruktor.thy` | `Isabelle/DeviceKonstruktor.lean` | 147 |
| 7 | `Verbund_Konstruktor.thy` | `Isabelle/VerbundKonstruktor.lean` | 141 |
| 8 | `Restrict_Alleinzugriff.thy` | `Isabelle/RestrictAlleinzugriff.lean` | 137 |

Total: 1417 Isar lines (statement says "about 1380" -- same order, the delta
is comments/blank lines).

## Counts: before / after

"Before" counts every `lemma`/`theorem`/`corollary`/`interpretation` of the
`.thy` file. "After" counts the Lean counterparts (same mathematical content).

| Theory | Before | After | Note |
|---|---|---|---|
| Accumulates_Monoid | 11 | 13 | `min` triple stated as 3 named theorems instead of 1 `shows ... and ... and ...`; 4 interpretations become 4 `MergeMonoid` terms |
| Gruppe_Erhaltung | 7 | 7 | plus helper `kette_steigt` |
| Format_Roundtrip | 3 | 3 | plus helpers `holtAux_eq`, `roundtrip_aux`, `nimm_succ` |
| Option_Sonderwert | 4 | 4 | |
| Consuming | 6 | 6 | plus helpers `wf_of_leer`, `wf_subset_unten`, `nicht_wf_bei_schlinge`, `kante_leer_wf` |
| Device_Konstruktor | 4 | 4 | |
| Verbund_Konstruktor | 4 | 4 | |
| Restrict_Alleinzugriff | 3 | 3 | |
| **Total** | **42** | **44** | |

Every ported statement is faithful (same quantifiers, premises, conclusion).
Nothing was left unported; no statement was weakened. Representation
adaptations (all documented in each file header) were necessary where Lean
core has no counterpart library:

- sets of pairs -> relations/predicates (`Gruppe`, `Device`, `Consuming`,
  `Restrict`; `W ⊆ less_than` becomes `∀ a b, W a b → a < b`);
- `Multiset` equality -> own `IsPerm` inductive (no `Multiset` in Lean core);
- `wf`/`wf_subset`/`acyclic`/`map_of`/`distinct` -> proved/defined locally
  (no relation library in Lean core);
- `type_synonym adresse = nat` -> `Nat` directly (a synonym IS `Nat`; a named
  `abbrev` would additionally hide the variables from `omega`, see below);
- `min` at `{linorder, order_top}` -> `min` on `Nat` with the top made an
  EXPLICIT premise (`∀ T a, a ≤ T → min T a = a`); the Isabelle `order_top`
  instance supplies silently what is now written down.

## Mapping tables

### 1. Accumulates_Monoid -> AccumulatesMonoid.lean

| Isabelle name | Lean name | Faithful |
|---|---|---|
| `merge_monoid` (locale) | `MergeMonoid` (structure) | yes |
| `rechts` | `rechts` | yes |
| `faltet` | `faltet` | yes |
| `faltet_anhaengen` | `faltet_anhaengen` | yes |
| `faltet_vertauschen` | `faltet_vertauschen` | yes |
| `faltung_ist_reihenfolgeunabhaengig` (`mset`) | `faltung_ist_reihenfolgeunabhaengig` (`IsPerm`) | yes (permutation = multiset equality) |
| `rmw_kette` | `rmwKette` | yes |
| `rmw_kette_zieht_heraus` | `rmw_kette_zieht_heraus` | yes |
| `am_ruhepunkt_gleich_dem_atomaren_rmw` | `am_ruhepunkt_gleich_dem_atomaren_rmw` | yes |
| `acc_max` / `acc_add` / `acc_or` / `acc_and` | `maxMonoid` / `addMonoid` / `orMonoid` / `andMonoid` | yes |
| `min_ist_monoid_mit_top` (3 parts) | `min_ist_monoid_vereinigen`, `min_ist_monoid_vertauschen`, `min_ist_monoid_mit_top` | yes (top explicit) |

### 2. Gruppe_Erhaltung -> GruppeErhaltung.lean

| Isabelle name | Lean name | Faithful |
|---|---|---|
| `rangordnung_azyklisch` | `rangordnung_azyklisch` | yes |
| `eine_kante_gegen_die_ordnung_reicht` | `eine_kante_gegen_die_ordnung_reicht` | yes |
| `zug` (locale) | `Zug` (structure) | yes (`zs ! i` -> `zs[i]? = some z`) |
| `zug.beobachtbar` | `beobachtbar` | yes |
| `zug.beobachtbares_gilt` | `beobachtbares_gilt` | yes |
| `paarig` / `ganzer_zug` / `abgebrochen` | `paarig` / `ganzerZug` / `abgebrochen` | yes |
| `ganzer_zug_ist_einer` | `ganzer_zug_ist_einer` | yes |
| `zwischenaustritt_bricht` | `zwischenaustritt_bricht` | yes |
| `abgebrochener_ist_kein_zug` | `abgebrochener_ist_kein_zug` | yes |
| `halber_abdruck_ist_kein_zug` | `halber_abdruck_ist_kein_zug` | yes |

### 3. Format_Roundtrip -> FormatRoundtrip.lean

| Isabelle name | Lean name | Faithful |
|---|---|---|
| `feld` / `liest` / `schreibt` | `Feld` / `liest` / `schreibt` | yes (`map` over range -> explicit `holtAux`; default `0` outside, never observed under the premise) |
| `roundtrip` | `roundtrip` | yes |
| `trennt` | `trennt` | yes |
| `schreiben_stoert_getrennte_felder_nicht` | `schreiben_stoert_getrennte_felder_nicht` | yes |
| `passt` | `passt` | yes |
| `eintrittspruefung_deckt_jeden_zugriff` | `eintrittspruefung_deckt_jeden_zugriff` | yes |

### 4. Option_Sonderwert -> OptionSonderwert.lean

| Isabelle name | Lean name | Faithful |
|---|---|---|
| `indextyp` | `indextyp` (predicate) | yes |
| `kodiere` | `kodiere` | yes |
| `sonderwert_ausserhalb` | `sonderwert_ausserhalb` | yes |
| `kodiere_injektiv` | `kodiere_injektiv` | yes |
| `kodiere_wort` | `kodiereWort` | yes |
| `sonderwert_kollidiert_bei_vollem_wort` | `sonderwert_kollidiert_bei_vollem_wort` | yes |
| `kodiere_wort_injektiv` | `kodiere_wort_injektiv` | yes |

M-2 (no generated computation reaches the special value) is a statement about
`emit.rs` and is unprovable in both registers; named in the Bridge section.

### 5. Consuming -> Consuming.lean

The `Table_Induktion.thy` model (`slot`, `tabelle`, `kante` with TWO edge
kinds) is restated in-file, attributed, because that theory is another lane's
half (not imported, not modified).

| Isabelle name | Lean name | Faithful |
|---|---|---|
| `verbrauche` | `verbrauche` | yes |
| `verbrauche_verkleinert` | `verbrauche_verkleinert` | yes |
| `ordnung_bleibt_unter_entfernen` | `ordnung_bleibt_unter_entfernen` | yes (`wf_subset` proved as `wf_subset_unten`) |
| `haenge_um` | `haengeUm` | yes |
| `umhaengen_kann_zyklus_erzeugen` | `umhaengen_kann_zyklus_erzeugen` | yes |
| `ist_blatt` / `waehlt_minimal` | `istBlatt` / `waehltMinimal` | yes |
| `blattheit_braucht_minimale_auswahl` | `blattheit_braucht_minimale_auswahl` | yes |
| `zeugen` | `zeugen` | yes |
| `leermenge` | `leermenge` | yes |
| `leermenge_ist_zustandsabhaengig` | `leermenge_ist_zustandsabhaengig` | yes |

### 6. Device_Konstruktor -> DeviceKonstruktor.lean

| Isabelle name | Lean name | Faithful |
|---|---|---|
| `reg` / `zelle` | `Reg` / `zelle` | yes |
| `getrennt` | `getrennt` | yes |
| `getrennte_register_treffen_getrennte_zellen` | `getrennte_register_treffen_getrennte_zellen` | yes |
| `trennung_haengt_nicht_an_der_basis` | `trennung_haengt_nicht_an_der_basis` | yes |
| `bankzelle` | `bankzelle` | yes |
| `bankeintraege_ueberlappen_nicht` | `bankeintraege_ueberlappen_nicht` | yes |
| `stride_null_macht_die_bank_leer` | `stride_null_macht_die_bank_leer` | yes |

### 7. Verbund_Konstruktor -> VerbundKonstruktor.lean

| Isabelle name | Lean name | Faithful |
|---|---|---|
| `wohlgeformt` | `wohlgeformt` | yes |
| `deckt` | `deckt` | yes (declaration ORDER, the stricter form, as in Isabelle) |
| `deckt_setzt_jedes_genau_einmal` | `deckt_setzt_jedes_genau_einmal` | yes |
| `deckt_laesst_keins_aus` | `deckt_laesst_keins_aus` | yes |
| `liest` (`map_of`) | `liest` | yes |
| `ablesung_ist_eindeutig` | `ablesung_ist_eindeutig` | yes |
| `jedes_feld_hat_einen_wert` | `jedes_feld_hat_einen_wert` | yes |

### 8. Restrict_Alleinzugriff -> RestrictAlleinzugriff.lean

| Isabelle name | Lean name | Faithful |
|---|---|---|
| `rumpf` | `Rumpf` | yes (access set as predicate) |
| `restrict_bedingung` | `restrictBedingung` | yes |
| `rahmen_vollstaendig` | `rahmenVollstaendig` | yes |
| `wurzeln_getrennt` | `wurzelnGetrennt` | yes |
| `restrict_gerechtfertigt` | `restrict_gerechtfertigt` | yes (H3 not needed, as in Isabelle) |
| `ohne_trennung_kein_restrict` | `ohne_trennung_kein_restrict` | yes |
| `unvollstaendiger_rahmen_traegt_nichts` | `unvollstaendiger_rahmen_traegt_nichts` | yes |

That `own` means exclusivity stays a named language decision on both sides.

## Bridges to the Lean semantics (rule 3)

No new bridge LEMMAS were proved: a bridge lemma would need cross-model
imports (abstract nat/list model vs. typed `Expr`/`World` model), and in each
case the overlap is either already tied or explicitly absent. Each file has a
Bridge section naming the status:

- Option_Sonderwert <-> `SchablonenT5Sem.lean` §4 (`sonderwert_disjoint`,
  `sonderwert_schranke`): complementary halves; the word half (`N < 2^w`) lives
  only here, the `eval` half only there.
- Device_Konstruktor <-> `SchablonenT5Sem.lean` §5 (model-facing half only);
  the layout arithmetic ported here has no counterpart there (no address cells
  in `World`) and vice versa.
- Gruppe_Erhaltung (a) <-> `SchablonenT5Sem.lean` §3 (`kette_steigt`,
  `kein_wartezyklus`, `sperrabdruck_form`); parts (b)/(c) have no counterpart
  in `execStmt` (no invariant parameter), stated in that file's CUTS.
- Format_Roundtrip: `hhi : hi + n ≤ D.count t` on `Expr.leseBytes` IS the entry
  check at the type level; the value-level write-then-read roundtrip has no
  `World.slots` counterpart yet -- named, the frame lemma it would need is
  identified.
- Accumulates_Monoid: the per-core layout and neutral-element choice is the
  PL.3 emitter bridge, unshown on both sides; the named trap
  `min_mit_null_start_zieht_auf_null` marks it.
- Consuming: bridge is the pointwise `kante` equality with the coming
  `Table_Induktion` port (another lane's half).
- Verbund_Konstruktor: the emitter establishing `deckt` is the PL.3 bridge,
  unshown on both sides (M-2 there).
- Restrict_Alleinzugriff: no counterpart exists (no `restrict` annotation, no
  frames/roots in the grammar) -- the theorem stands as pure mathematics, as
  in Isabelle.

## Witnesses (rule 6)

No ported lemma quantifies over syntax (`Expr`/`Stmt`/grammar terms): all 42
quantify over data (lists, nats, tables, relations). The inhabitation
obligation is therefore vacuous. Data-level `NAME_zeuge` witnesses on concrete
instances are provided in every file anyway, following house convention:

- `faltet_zeuge` (fold `[1,2,3]` = 6, order-independent),
- `rangordnung_zeuge` (the `{(0,1),(1,0)}` cycle vs. acyclic `{(0,1)}`),
- `roundtrip_zeuge` (write `[7,8]` at offset 4, read back; entry check),
- `kodiere_zeuge` (`N = 3` apart, `N = 4 = 2^2` collapsed),
- `verbrauche_zeuge` (consuming place 0 removes the only edge),
- `zelle_zeuge` (offsets 0/8 width 4; bank stride 16),
- `verbund_zeuge` (`[("x",1),("y",2)]` reads back),
- `restrict_zeuge` / `restrict_gegenzeuge` (single-root body justified,
  aliased body refused).

## Toolchain findings (for the record, not findings about the tree)

1. **`omega` is blind to `abbrev`-typed variables.** Measured: `omega` fails on
   a goal over `j : Idx` with `abbrev Idx := Nat` ("No usable constraints
   found... You may need to unfold definitions"), while the identical goal
   over `Nat` closes. Consequence: `DeviceKonstruktor.lean` uses `Nat`
   directly (a `type_synonym` IS `Nat`); `OptionSonderwert.lean` proves its
   three arithmetic steps with `Nat.ne_of_lt`/`Nat.lt_trans` instead of
   `omega`. `decide`/`rfl` are unaffected (kernel unfolds the abbrev).
2. **`by_cases ... with | inl/inr` does not attach in this toolchain**
   (goals stay open as `pos`/`neg`); `rcases Decidable.em ... with ...` and
   plain `cases` work. All new files use the latter.
3. **`WellFounded` is inductive here** (`WellFounded.intro`), not a
   definition; `constructor`-style proofs must go through `.intro`.
4. **`simp only [Nat.add_assoc]`-style simp calls make no progress** on
   `Nat.add`-stated goals in this core version; the term proofs
   (`assoz := Nat.add_assoc`) typecheck. `Prod.mk_eta` does not exist in core.
5. `#print axioms` for the new files shows at most
   `[propext, Classical.choice, Quot.sound]` -- exactly the set every existing
   `Grammatik/*.lean` file already lists (including `rfl` theorems, via the
   imported model definitions). One quirk mapped: `omega` closing a
   conjunction that mentions `List.length` atoms pulls `Classical.choice`;
   splitting the goal first (`constructor` + two `omega`s) does not. The
   remaining `Classical.choice` entries come from that quirk and match house
   style; no file uses `sorry`, `axiom`, or `native_decide`.
