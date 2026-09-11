# Port migration: Deklaration old → new (shared-flag removal)

Base: `58d6b83` (lane-112). Source of the change: the WIP `Syntax.lean`
`Deklaration` diff (commit `85cb4f4`, read-only; stale base, NOT mergeable as
is — used here only as prior art for the mapping rules).

## 1. The delta (old → new)

REMOVED from `structure Deklaration` (`grammatik/Grammatik/Syntax.lean`):

| Removed | Old shape |
|---|---|
| `geteilt : Tab → Bool` | per-table shared flag |
| `ggeteilt : Glob → Bool` | per-global shared flag |
| `geteilt_bewacht` | `∀ t, geteilt t = true → braucht t ≠ []` |
| `ggeteilt_bewacht` | `∀ g, ggeteilt g = true → gbraucht g ≠ [] ∨ atomar g = true` |

ADDED:

| Added | New shape |
|---|---|
| `braucht_alle` | `∀ t, braucht t ≠ []` — EVERY carrier has a guard (lock or owner mark) |
| `gbraucht_alle` | `∀ g, gbraucht g ≠ [] ∨ atomar g = true` |
| `braucht_eigner` | `∀ t m s, Sum.inr (m, s) ∈ braucht t → m ∈ eigner t` |
| `gbraucht_eigner` | `∀ g m s, Sum.inr (m, s) ∈ gbraucht g → ∃ t, m ∈ eigner t` |
| `invarianten_marken` | writer of an invariant carrier holds ALL its carriers' owner marks (`konsumiert`) |
| `geist : Tab → Bool` | ghost table: spec-only memory |
| `ggeist : Glob → Bool` | ghost global: spec-only memory |

(`eigner : Tab → List Marke` already exists at `Syntax.lean:144`; the new
fields reference it. No other file uses `geist`/`braucht_alle`/… yet —
zero hits outside `Syntax.lean`.)

## 2. Per-file break/clean table (all 23 files, base `58d6b83`)

BREAKS = names a removed declaration (`D.geteilt`, `D.ggeteilt`,
`D.geteilt_bewacht`, `D.ggeteilt_bewacht`, or a `Deklaration where` instance
field for one of them). CLEAN = elaborates unchanged once the new
`Deklaration` is in place (pass-through uses of `Gesittet`/`kein_wettlauf`
do NOT break — signatures are unchanged by the WIP port).

| File | Verdict | Evidence (base line numbers) |
|---|---|---|
| `Syntax.lean` | ORIGIN (the change itself) | removes `:128-129`, `:178`, `:183`; adds `braucht_alle` etc. |
| `Extraktion.lean` | BREAKS (reads + instance) | reads `D.geteilt` at `:230`, `:259`, `:326`; `D.ggeteilt` at `:239`, `:281`, `:337` (defs `geteiltTab`, `geteiltGlob`, theorems `…_trifft`, `geteiltAus_tab`, `geteiltAus_glob`); instance `miniD` fields at `:624-625` (`geteilt`, `ggeteilt`), `:655`, `:657` (`geteilt_bewacht`, `ggeteilt_bewacht`) |
| `Wettlauf.lean` | BREAKS (premise + proofs) | W5 field `ungeteilt` at `:192-195` (`D.geteilt`…`= false` / `D.ggeteilt`…`= false`); by-contradiction blocks at `:385-388`, `:418-421`; `D.geteilt_bewacht` at `:389`; `D.ggeteilt_bewacht` at `:422`; mirror premise at `:621-627` (`gesittet_aus_einfaedig`) |
| `Satz.lean` | BREAKS (instance only) | instance `leer` fields at `:1355-1356` (`geteilt`, `ggeteilt`), `:1386`, `:1388` (`geteilt_bewacht`, `ggeteilt_bewacht`) |
| `Zeugnis.lean` | BREAKS (instance only) | instance `TestD` fields at `:636-637`, `:665`, `:667` |
| `InterferenzAllgemein.lean` | BREAKS (def + 2 uses) | `def Geteilt` at `:119-121` (`D.geteilt` / `D.ggeteilt`); used at `:203` (`GeteiltGedeckt`), `:509` (`GeteiltGedecktMitAusnahmen`) |
| `Geraet.lean` | BREAKS (def + 1 use) | `def DmaSichtbar` at `:122` (`D.geteilt t = true`); used at `:146` (`GeraetWache.sichtbar`) |
| `Geteilt.lean` | CLEAN (stale docs only) | own `Bau.geteilt` field at `:84`, instance at `:355` is NOT `Deklaration.geteilt` — untouched; only doc lines `:7`, `:35`, `:83` name `D.geteilt`/`D.ggeteilt` (reword, no proof impact) |
| `Ziel.lean` | CLEAN | passes `hg : Gesittet l` through at `:122-138`; no removed name (`:22` "Die Zeit ist geteilt" is prose about time) |
| `Unterbrechung.lean` | CLEAN | uses `hg.gut` (`:74-77`, field unchanged), passes `hg` through at `:107`, `:124` |
| `Interferenz.lean` | CLEAN | `kein_wettlauf` only in comments (`:50`, `:55`); `hGesittet` at `:138` is opaque pass-through |
| `Adressraum.lean` | CLEAN | zero hits |
| `Budget.lean` | CLEAN | zero hits |
| `Erhaltung.lean` | CLEAN | zero hits |
| `Fehler.lean` | CLEAN | zero hits |
| `Fristlauf.lean` | CLEAN | zero hits |
| `Koernung.lean` | CLEAN | zero hits |
| `Komposition.lean` | CLEAN | zero hits |
| `Marken.lean` | CLEAN | zero hits (`marke_eindeutig` only in comments `:44`, `:61`, `:201`) |
| `Semantik.lean` | CLEAN | zero hits |
| `Terminierung.lean` | CLEAN | zero hits |
| `Typen.lean` | CLEAN | zero hits |
| `Zucker.lean` | CLEAN | zero hits |

Count: 6 BREAKS + 1 ORIGIN + 1 CLEAN-with-docs (`Geteilt.lean`) + 15 CLEAN = 23.

Disambiguation that matters: `Extraktion.lean:375`
(`bauAus … : Geteilt.Bau`, `geteilt := geteiltAus …`) fills `Bau.geteilt`,
not `Deklaration.geteilt` — it survives; only its *source* (`geteiltAus`
over `D.geteilt`/`D.ggeteilt`) breaks (class I below).

## 3. Mechanical mapping per breakage class

Classes A–E are verbatim the WIP `Wettlauf.lean` port (`85cb4f4` diff,
`58d6b83…85cb4f4 -- grammatik/Grammatik/Wettlauf.lean`).

- **A. Guarded-table premise → unconditional.** `have hb := D.geteilt_bewacht t hget`
  becomes `have hb := D.braucht_alle t` (`Wettlauf.lean:389`).
- **B. Guarded-global case split → unconditional split.** `rcases D.ggeteilt_bewacht x hget
  with hb | ha` becomes `rcases D.gbraucht_alle x with hb | ha` — same
  disjunction shape, proofs under each branch unchanged (`:422`).
- **C. W5 by-contradiction blocks → DELETE.** The 4-line
  `have hget : D.geteilt t = true := by apply Classical.byContradiction; …`
  (`:385-388`, `:418-421`) disappears; every carrier is guarded now, no case
  split on sharedness remains.
- **D. `Gesittet.ungeteilt` field → DELETE** (`:192-195`); drop the mirror
  `ungeteilt` argument of `gesittet_aus_einfaedig` (`:621-627`).
- **E. `marke_eindeutig` calls gain an owner witness.** Table case:
  `hg.marke_eindeutig … hi hj hmi hmj` becomes
  `hg.marke_eindeutig … ⟨t, D.braucht_eigner t m s hwt⟩ hi hj hmi hmj`;
  global case: `(D.gbraucht_eigner x m s hwt)` in the same position.
  (WIP tightens W4 to owner marks: new hypothesis
  `(∃ t, m ∈ D.eigner t)` on the field.)
- **F. `Deklaration where` instances: delete 4 fields, add 7.**
  Delete `geteilt :=`, `ggeteilt :=`, `geteilt_bewacht :=`,
  `ggeteilt_bewacht :=`; add `braucht_alle`, `gbraucht_alle`,
  `braucht_eigner`, `gbraucht_eigner`, `invarianten_marken`, `geist`,
  `ggeist`. Fill per instance:
  - `Satz.leer` (both carriers `Empty`): every new proof field is `…_elim`
    (`fun t => t.elim` / `fun g => g.elim` / `fun _ i => i.elim`);
    `geist`/`ggeist` are `fun t => t.elim` / `fun g => g.elim`.
  - `Zeugnis.TestD` (`braucht`/`gbraucht = [.inl ()]`, `eigner = []`,
    `Inv = Empty`): `braucht_alle`/`gbraucht_alle` by `simp`;
    `braucht_eigner`/`gbraucht_eigner` vacuous (`Sum.inr … ∈ [.inl ()]`
    is `False` — `by simp at h`); `invarianten_marken` by `i.elim`;
    `geist`/`ggeist := fun _ => false`.
  - `Extraktion.miniD` — OBSTACLE: `braucht := fun _ => []` cannot satisfy
    `braucht_alle`, and `Lock = Empty` / `Marke = Empty` leave no guard
    inhabitant. The lane must extend `miniD` (e.g. `Lock := Unit`,
    `braucht := fun _ => [.inl ()]`); `gbraucht_alle`/`gbraucht_eigner`
    stay `nomatch`/`elim` (`Glob = Empty`); `geist`/`ggeist := false`.
- **G. `InterferenzAllgemein.Geteilt` (`:119-121`) → rephrase, lane decision.**
  "Shared" as reachability no longer exists; every co-written carrier is
  guarded by construction. Options, ranked: (1) drop the `Geteilt c = true ∧`
  conjunct in `GeteiltGedeckt` (`:203`) and `…MitAusnahmen` (`:509`) —
  co-writing IS the coverage trigger; (2) redefine via guard non-emptiness
  (vacuously true — documents nothing); (3) redefine via
  `D.geist c = false` (executable co-writing). Downstream is file-local
  (`:203`, `:429`, `:505-509`).
- **H. `Geraet.DmaSichtbar` (`:122`) → rephrase, lane decision.**
  Suggested: `D.geist t = false` — the device writes executable memory,
  never ghost; downstream `GeraetWache.sichtbar` (`:146`) unchanged in shape.
- **I. Extraktion `geteiltTab`/`geteiltGlob`/`geteiltAus` + 5 theorems
  (`:225-351`) → DELETE or repurpose, lane decision.** `bauAus.geteilt`
  (`:375`) still fills `Geteilt.Bau.geteilt` (survives), but its source is
  gone. Options, ranked: (1) constant-`true` feed (fail-closed, matches the
  proven `geteiltAus_fremd` stance — unknown means shared); (2) feed from
  `!geist`; (3) delete `Bau.geteilt` + `pruefeUngeteilt` chain — largest
  blast radius (speech probes `geteilt_treu_aus_bau`,
  `ungeteilt_aus_baulauf_aus_bau` at `:532-576` lose their consumer with W5
  gone). Feedback into `miniD` (class F obstacle) belongs to this lane.
- **J. Stale docs (no proof impact, reword along the way):** `Geteilt.lean`
  `:7`, `:35`, `:83`; `Syntax.lean:61`; `Wettlauf.lean:21`;
  `InterferenzAllgemein.lean` §§1–4 headers; `Extraktion.lean` §§4, 9
  comments; `Geraet.lean:27`.

## 4. Suggested lane order (leaves first, import graph at base)

`Satz → Wettlauf → {Geraet, Unterbrechung, Ziel, Interferenz} → InterferenzAllgemein`;
`Extraktion → {Geteilt, Wettlauf, Interferenz, InterferenzAllgemein}`;
`Zeugnis → Syntax` only. Downstream pass-through files (`Ziel`,
`Unterbrechung`, `Interferenz`) need NO lane — they re-elaborate once
`Wettlauf` lands.

1. **Satz** (leaf; instance `leer` proves the class-F `Empty` fill pattern).
2. **Zeugnis** (leaf, independent of 1; class-F non-empty fill pattern).
3. **Wettlauf** (needs 1 elaborated only in the build sense; classes A–E,
   verbatim WIP mapping).
4. **InterferenzAllgemein** (class G decision; carries opaque `hGesittet`,
   so blocked on 3 only for the build).
5. **Geraet** (class H decision; blocked on 3 only for the build).
6. **Extraktion** (classes F-obstacle + I; imports all of 1–5; heaviest —
   `miniD` extension plus speech-probe rewiring).
7. `Geteilt.lean` doc touch-up (class J) rides any lane — CLEAN, no dependency.
