# MUSE-REPORT-168 -- Isabelle to Lean port (7 theories)

Lane 168. The seven theories are ported completely: every `lemma` /
`theorem` / `corollary` has a Lean counterpart with the same quantifiers,
premises and conclusion. 63 statements in, 63 out, all faithful. No
statement had to be left unported.

## Files

New, one per theory, under `grammatik/Grammatik/Isabelle/`, wired into
`grammatik/Grammatik.lean` (7 added imports):

| Theory | Lean file | Lines |
|---|---|---|
| `Table_Induktion` | `Grammatik/Isabelle/Table_Induktion.lean` | 152 |
| `Table_Indexschranke` | `Grammatik/Isabelle/Table_Indexschranke.lean` | 152 |
| `Table_Absenkung` | `Grammatik/Isabelle/Table_Absenkung.lean` | 75 |
| `Table_Zaehlung` | `Grammatik/Isabelle/Table_Zaehlung.lean` | 332 |
| `Table_Ops_Erhaltung` | `Grammatik/Isabelle/Table_Ops_Erhaltung.lean` | 546 |
| `Absenkung_Parametrisch` | `Grammatik/Isabelle/Absenkung_Parametrisch.lean` | 544 |
| `Intervall_Aussen` | `Grammatik/Isabelle/Intervall_Aussen.lean` | 145 |

`beweise/` is untouched (booking Isabelle out is a later step).

## Evidence

- `./lean-bau` (full `lake build`): **Build completed successfully
  (161 jobs)**, exit 0, no errors in the new files, no new warnings.
- `./cargo-pruef` (full `cargo build` + `cargo test --no-fail-fast`):
  exit 0, 0 failing (no Rust touched; control run).
- `grep` over the 7 files: no `sorry`, no `axiom`, no `native_decide`.
- Sampled `#print axioms`: `table_induktion_zwei_kanten`,
  `umhaengen_erhaelt`, `aliasbruch_bricht_die_absenkung` depend on no
  axioms at all; `buchfuehrung_erhaelt`,
  `absenkung_am_belegten_platz` on `[propext, Quot.sound]`;
  `summe_liegt_in_der_gerechneten_schranke` on `[propext]`. Standard
  core axioms only (from `simp`/`rw`/`if` machinery).
- `decide` is used only on closed concrete goals over structurally
  recursive or non-recursive definitions (the permitted kernel
  evaluation); never `native_decide`.

## Representation explications (apply to all tables below)

All mappings are faithful; the following explications were needed
because this project has no mathlib and no real library. In each case
the mathematical content is unchanged:

- (E1) Isabelle sets (`{i. i < N}`, `(idx x idx) set`) are predicates
  (`Nat -> Prop`, `Nat -> Nat -> Prop`); set equality is predicate
  (function) equality.
- (E2) `finite S` is `Endlich p` (an explicit bound list,
  `List.range N` is the bound). No set library exists here.
- (E3) `card {s. s < n /\ P s}` is `((List.range n).filter P).length`.
  The range enumerates exactly the set below the bound.
- (E4) `Suc t` is `t + 1` (definitionally equal in Lean).
- (E5) `im_bereich` (an Isabelle `bool`) is a `Prop`.
- (E6) `real` (Complex_Main) is an abstract type `R` with abstract
  order `le` and addition `add`; `add_mono`, order reflexivity and
  transitivity are explicit per-lemma premises (Isabelle's `assumes`
  lines). The real instance recovers the originals.
- (E7) Locales are explicit parameters: `traeger` is section-free
  explicit arguments (`wirkung`, `online`, `je_operation` as a premise);
  `zielraum`/`zielsemantik` are Lean structures (`extends`);
  `rundung` is parameters plus per-lemma premises.
- (E8) `primrec` is `def` (structural recursion); `record` is
  `structure`; `inductive ... for σ` is `inductive` with `σ` as a
  parameter; `type_synonym` is `abbrev`/`def`.
- (E9) Function update `f(s0 := b)` is a local `upd` (this core has no
  `Function.update`).
- (E10) Predicates `nat => bool` are `Nat -> Bool`, written with
  `decide`.
- (E11) The two `interpretation` proofs (alias break, sonderwert
  break) are structure instances (`aliasbruch`, `sonderwert_inst`);
  the healthy target for the witnesses is `gesund` (plus `gesundFrei`
  for the free-slot witnesses, whose occupancy must read false).

## Mapping tables

`F` = faithful. Counts are `lemma` + `theorem` + `corollary`.

### 1. Table_Induktion -- 5 before, 5 after (+ 5 witnesses)

Model ported: `slot` record, `tabelle`, `kante` (both edge kinds),
`im_bereich`.

| Isabelle | Lean | F |
|---|---|---|
| `table_induktion` | `table_induktion` | yes |
| `blatt_ohne_eigene_klausel` | `blatt_ohne_eigene_klausel` | yes |
| `table_induktion_zwei_kanten` | `table_induktion_zwei_kanten` | yes |
| `kante_bleibt_im_bereich` | `kante_bleibt_im_bereich` | yes (E1) |
| `traeger_endlich` | `traeger_endlich` | yes (E1, E2) |

Witnesses on the empty table (`zσ`): `table_induktion_zeuge`,
`blatt_ohne_eigene_klausel_zeuge`,
`table_induktion_zwei_kanten_zeuge`,
`kante_bleibt_im_bereich_zeuge`, `traeger_endlich_zeuge`.

### 2. Table_Indexschranke -- 6 before, 6 after (+ 4 witnesses)

Model ported: `indextyp`, `belegt`, `wohlgeformt`,
`schreibstellen_im_typ` (all with E1; `'a option` is `Option α`).

| Isabelle | Lean | F |
|---|---|---|
| `indextyp_endlich` | `indextyp_endlich` | yes (E1, E2) |
| `indextyp_schranke` | `indextyp_schranke` | yes (E1) |
| `belegt_liegt_im_indextyp` | `belegt_liegt_im_indextyp` | yes |
| `indextyp_deckt_nicht_nur_belegte` | `indextyp_deckt_nicht_nur_belegte` | yes |
| `kette_bleibt_im_typ` | `kette_bleibt_im_typ` | yes |
| `im_bereich_folgt_aus_indexschranke` | `im_bereich_folgt_aus_indexschranke` | yes |

Witnesses on the one-slot table (`zσ`, `zfeld`):
`belegt_liegt_im_indextyp_zeuge`,
`indextyp_deckt_nicht_nur_belegte_zeuge`,
`kette_bleibt_im_typ_zeuge`,
`im_bereich_folgt_aus_indexschranke_zeuge`.
(`indextyp_endlich`, `indextyp_schranke` have no syntax premises.)

### 3. Table_Absenkung -- 4 before, 4 after (+ 0 witnesses)

Model ported: `indextyp`, `feldindizes` (both with E1).

| Isabelle | Lean | F |
|---|---|---|
| `zu_kurz_laesst_einen_index_ohne_speicher` | same name | yes (E1) |
| `zu_lang_laesst_speicher_ohne_index` | same name | yes (E1) |
| `absenkung_deckt_genau` | same name | yes (E1) |
| `kein_zugriff_laeuft_aus_dem_feld` | same name | yes (E1) |

No witnesses needed: all premises are pure naturals, and the two
`exists` conclusions already exhibit their witnesses (`m`, `N`) inside
the proofs. The M-3 emission half has no formal counterpart, same
boundary as in the theory.

### 4. Table_Zaehlung -- 12 before, 12 after (+ 5 witnesses)

Model ported: `zaehle`, `schritte`, `doppelt` (all E8), `upd` (E9).

| Isabelle | Lean | F |
|---|---|---|
| `zaehle_kongruent` | same name | yes |
| `zaehle_ist_kardinalitaet` | same name | yes (E3) |
| `zaehle_beschraenkt` | same name | yes |
| `zaehlung_faellt_um_eins` | same name | yes (E4, E9, E10) |
| `zaehlung_steigt_um_eins` | same name | yes (E4, E9, E10) |
| `zaehlung_bleibt_sonst` | same name | yes (E9, E10) |
| `buchfuehrung_erhaelt` | same name | yes (E9, E10) |
| `schritte_der_inneren` | same name | yes |
| `doppelte_schleife_kostet_produkt` | same name | yes |
| `doppelt_ist_mehr_als_einfach` | same name | yes |
| `erhaltung_faellt_ohne_schranke` | same name | yes (E9, E10) |
| `belegung_ist_nicht_mitgezaehlt` | same name | yes (E10) |

Witnesses on the constant table (`f` names `0` everywhere, slot `0`
rewritten to `1`): `zaehle_kongruent_zeuge`,
`zaehlung_faellt_um_eins_zeuge`, `zaehlung_steigt_um_eins_zeuge`,
`zaehlung_bleibt_sonst_zeuge`, `buchfuehrung_erhaelt_zeuge`.
(Z-1, Z-2, the cost lemmas and the two counterexamples are closed or
premise-free over syntax.)

### 5. Table_Ops_Erhaltung -- 18 before, 18 after (+ 11 witnesses)

Model ported: locale `traeger` (E7), `laufen`, `erreichbar`, `slot`
(E8), `erreicht` and `ueber` inductives (E8, same constructors),
`wohlgeformt`, `blatt`, `einfuegen`, `blatt_loeschen`, `umhaengen`,
`zwei`, `setze_eins`, `eigen`, `verbindend`.

| Isabelle | Lean | F |
|---|---|---|
| `folge_erhaelt` | same name | yes (E7) |
| `erreichbares_erhaelt` | same name | yes (E7) |
| `erreicht_bleibt_bei_frischem` | same name | yes (E9) |
| `einfuegen_erhaelt` | same name | yes |
| `erreicht_ohne_blatt` | same name | yes |
| `blatt_loeschen_erhaelt` | same name | yes |
| `umhaengen_ausserhalb` | same name | yes |
| `umhaengen_durch_s` | same name | yes |
| `umhaengen_erhaelt` | same name | yes |
| `umhaengen_erhaelt_am_belegten_platz` | same name | yes |
| `zwei_wohlgeformt` | same name | yes |
| `zyklus_erreicht_nichts` | same name | yes |
| `umhaengen_faellt` | same name | yes |
| `gegenbeispiel_erfuellt_die_alten` | same name | yes |
| `gegenbeispiel_verletzt_die_neue` | same name | yes |
| `eigen_bleibt` | same name | yes |
| `zweiter_traeger_unberuehrt` | same name | yes |
| `verbindung_nicht_gedeckt` | same name | yes |

Witnesses: `folge_erhaelt_zeuge`, `erreichbares_erhaelt_zeuge` (identity
operation, trivial invariant); on the witness table `wσ` (root at `0`,
slot `5` free): `erreicht_bleibt_bei_frischem_zeuge`,
`einfuegen_erhaelt_zeuge`, `erreicht_ohne_blatt_zeuge`,
`blatt_loeschen_erhaelt_zeuge`, `umhaengen_ausserhalb_zeuge`,
`umhaengen_ausserhalb_belegt_zeuge`, `umhaengen_durch_s_zeuge`,
`umhaengen_erhaelt_zeuge`,
`umhaengen_erhaelt_am_belegten_platz_zeuge` (at the occupied slot `0`,
since the corollary's extra premise needs one). The `zwei`
lemmas and the `setze_eins` lemmas are closed concrete statements and
need no instantiation. `ueber_wσ_inv` (inversion: `ueber` over `wσ`
collapses to equality) supports the `¬ Ueber` premises.

### 6. Absenkung_Parametrisch -- 13 before, 13 after (+ 7 witnesses)

Model ported: `abbild`, locales `zielraum`/`zielsemantik` (E7,
structures), the toy target (`wlies`, `wschreib`, `wbelegtort`,
`wdeutebelegt`, `wwort`, `gort`, `gdeute`, `gwirkung`, `dgort`,
`dgdeute`, `dgwirkung`); `umhaengen` etc. imported from (5).

| Isabelle | Lean | F |
|---|---|---|
| `anderer_platz_unberuehrt` | same name | yes |
| `belegung_von_s_unberuehrt` | same name | yes |
| `absenkung_am_belegten_platz` | same name | yes |
| `relabel_am_freien_platz_ist_wirkungslos` | same name | yes |
| `absenkung_geht_am_freien_platz_auseinander` | same name | yes |
| `absenkung_relabel` | same name | yes |
| `relabel_erhaelt_wohlgeformt` | same name | yes |
| `aliasbruch_verletzt_E4` | same name | yes |
| `aliasbruch_bricht_die_absenkung` | same name | yes |
| `sonderwert_haelt_E4` | same name | yes |
| `sonderwert_haelt_E5` | same name | yes |
| `sonderwert_verletzt_E6` | same name | yes |
| `sonderwert_bricht_die_absenkung` | same name | yes |

Witnesses on `gesund` (separating slots, disjoint occupancy, faithful
decoding, occupancy reads true) and `gesundFrei` (same, occupancy
reads false, for the two free-slot lemmas): one `NAME_zeuge` per
locale theorem (7). The alias/sonderwert lemmas are closed concrete
statements.

### 7. Intervall_Aussen -- 5 before, 5 after (+ 5 witnesses)

Model ported: locale `rundung` (E6, E7), `aussen_lo`/`aussen_hi`.

| Isabelle | Lean | F |
|---|---|---|
| `huelle_haelt` | same name | yes (E6) |
| `monoton_unten` | same name | yes (E6) |
| `monoton_oben` | same name | yes (E6) |
| `summe_liegt_in_der_gerechneten_schranke` | same name | yes (E6) |
| `exakt_wandert_nicht` | same name | yes (E6) |

Witnesses on the `Int` instance with exact arithmetic
(`fl = nd = nu = id`; `Int.add_le_add`, `Int.le_refl`, `Int.le_trans`
discharge the premises): one `NAME_zeuge` per lemma (5).

## Totals

63 statements before, 63 after, all faithful, none left listed.
Witnesses: 0 + 4 + 5 + 5 + 11 + 7 + 5 = 37 `NAME_zeuge` theorems for
every ported lemma whose premises quantify over syntax (closed
concrete lemmas and pure-arithmetic lemmas are exempt by the rule).

## Bridges (rule 3)

No new bridge lemma was added; the existing ties are named instead:

- `Table_Indexschranke` / `Table_Absenkung`: the carrying halves over
  the real semantics are already tied in
  `Grammatik.SchablonenT5Sem` (sections 1 and 2). No direct bridge
  from the standalone index predicates: `World.slots` is total, so the
  occupancy half has no counterpart there (documented in that file),
  and the standalone `{i. i < N}` predicates admit no direct embedding
  into `Expr ... (.index n)`.
- `Table_Induktion`, `Table_Zaehlung`, `Table_Ops_Erhaltung`,
  `Absenkung_Parametrisch`, `Intervall_Aussen`: no counterpart in the
  Lean grammar model -- the induction schema over the generator's slot
  model, the declined `count` aggregation (no `count` syntax in
  `Syntax.lean`), the hand-defined model mutations (emitted C bodies
  are not proved to be these functions), the C/machine target
  properties E1--E6, and the checker-side float computation. A bridge
  in each case would need a new embedding definition, i.e. precisely
  the unproved correspondence the theories bound -- not straightforward,
  so named here instead.

## Core constraints met while porting (for the next lane)

This core (v4.33.1, no mathlib) lacks: `Function.update`,
`by_contra`, `rcases`, `Nat.lt_step`, `ne_of_lt`; section
`variable (h : Prop)` hypotheses are not usable inside proofs (all
assumes are explicit per-lemma binders); `WellFounded` needs
`WellFounded.intro` (it is not transparent); `Option.noConfusion`
needs its type-equality argument first (`cases h` on a constructor
clash is the working idiom); `set_option ... in` / `omit ... in`
cannot follow a doc comment (file-wide options used instead);
`simp [plain-def]` unfolding is unreliable here -- concrete `if`
definitions are unfolded with `show` + `rw [if_pos/if_neg]`, while
`simp [recursive-def]` via equation lemmas works.
