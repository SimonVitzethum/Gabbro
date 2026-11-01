/-
  File:       Grammatik/Erhaltung.lean
  Subject:    The PRODUCER CONTRACT as Lean shapes: correspondence, alias,
             cost, ruling table, rechecker shape, and priced admissions.
             Design plus checked legs; the semantic rulings stay cut.

  Claim (in one sentence):
    The file turns the emitter contract into data (certificate rows,
    alias obligation, cost claim, ruling table with priced statuses) and
    proves the Lean-side legs that hold without C semantics: every
    recomputation whose success IMPLIES its sentence (§§6-8), the priced
    admissions as table data (§11), and the table now CLOSED
    (`tafel_geschlossen`) -- while the per-slot semantic adequacy, the
    certificate producer, C execution meaning, and the rechecker program
    stay cut.

  What the file actually contains (§ by §):
    §1  Correspondence as data plus four Prop shapes: `CorrSite` /
        `CorrCert` rows, `corrComplete` / `corrOrdered` / `corrClosed` /
        `corrNoExtra`, and the assembled sentence `satz_korrespondenz`.
    §2  Alias as data: `ArithSource`, `AliasObligation`
        (address-arithmetic sites carried openly), `aliasKept`
        (empty site list), census number `ptrArithCensus = 491`.
    §3  Cost as data: `CostCarrier` (CerCo vs production), `CostClaim`,
        `costKept` (CerCo only), `costMeasured` (production needs a
        pair), `senkungBegrenzt` (at most `proPrimitiv` C statements
        per primitive).
    §4  Ruling table: `RulingStatus` (`offen` / `aufListe` price /
        `ausErzeuger`), the 30 census slots `OffeneForm`
        (C1 = 7, C2 = 19, C3 = 4) plus the syscall boundary slot
        `syscallStub`, the `?:` template
        `bedingtEntscheid`, rows `EntscheidZiel`, prices
        `beschraenktPreis` / `fluechtigPreis`, the table `tafel`
        (19 named shapes admitted with price), `entschieden`,
        and the sentences `satz_korrespondenz` / `satz_alias` /
        `satz_kosten` / `satz_tafel` / `satz_erzeugervertrag`
        (shapes only, §5).
    §6  Correspondence recomputation: Boolean legs `vollB` /
        `ohneExtraB` / `geordnetB` / `geordnetCertB` / `ruledB` /
        `geschlossenB` / `pruefeKorrespondenz` with soundness theorems
        (`vollB_sound`, `ohneExtraB_sound`, `geordnet_sound`,
        `geordnetCertB_sound`, `ruledB_sound`, `ruledB_voll`,
        `geschlossenB_sound`, `geschlossen_immer`,
        `korrespondenz_aus_vieren`, `korrespondenz_sound`,
        `korrespondenz_leer`), each with accept/reject `example`s.
    §4b Witness-pair linkage (C2 shape): `ZeugenPaar`
        (probe name, C form, expected outcome), `zeugenPaarGueltig`
        (form tabled, probe name non-empty), `zeugenPaar_sound`,
        the five measured pairs `c2Paare` under
        `messung/proben/zeugnis-c2/`, `c2AlleGueltig` /
        `c2Alle_decided` (green by `decide`), `c2Paar_gedeckt`.
    §6b Emitted witness (C1 shape): `emittedMarker` (`gabbro-site`,
        written by `emit.rs` `emittiere_mit`), `emittedRowFields` /
        `cformWort` (mirror of `corrcert.rs` rows, witnessed by
        `messung/proben/corrcert/korr-*.json`), `markerStimmtB`
        (marker-vs-row agreement, accept/reject `example`s).
    §7  Alias discharge: `alias_leer` (empty list keeps the
        obligation), `census_steht` (491 as data), accept/reject
        `example`s including the honest reject of today's full
        census image.
    §8  Cost legs: `kosten_cerCo_gilt`, `kosten_produktion_frei`
        (production claims nothing on the CerCo leg),
        `gemessen_produktion` (needs carrier plus pair),
        `gemessen_cerCo_frei`, `traeger_trennt`,
        `senkung_aus_schranke` (17 per primitive from
        `messung/ABSENKUNG-MESSUNG.md`), `kosten_satz_bauen`,
        both-directions `example`s at the measured number.
    §9  Debt proved real, then closed: `tafel_geschlossen`
        (`satz_tafel` by `decide` -- the last slot is now ruled
        with price) and `vertrag_braucht_tafel` (the contract
        NEEDS the table, as a projection, not an assumption).
    §10 Rechecker as program SHAPE (draft, no `theorem`):
        `NachprueferEingabe` (run artefacts in), `nachpruefer`
        (recompute to a verdict), `nachprueferGueltig`,
        `satz_nachpruefung_vertrauen` (valid verdict means
        trustworthy certificate -- linkage shape only).
    §11 Five priced slots as data: `logUndOderEntscheid` /
        `fortEntscheid` / `abbruchEntscheid` / `zeigerIndexEntscheid`
        (admissions with price from `messung/CFORM-REGEL-*.md`),
        `tafelPreisNachtrag` / `tafelStatusNeu` / `tafelNeu`
        (same rows, five statuses decided), `satz_tafelNeu`
        (shape, still draft).
    Every theorem ends with a `#print axioms` line: Lean's standard
    axioms (`propext`, `Quot.sound`, plus `Classical.choice` where
    the build reports it) only.

  What stays cut (no C semantics, no producer, no adequacy):
    C1  Lean PRODUCES no certificate; the second program stays
        `instrumente/nachpruefer.py`. The correspondence now NAMES
        its image (§6b) but the reader program is not here.
    C2  What a C form MEANS stays cut (C-semantics execution);
        the witness-pair LINKAGE is a checked shape (§4b), and the
        common-mode failure (both tables from one text) is named,
        not closed.
    C3  `restrict` and `volatile` stay trust: priced option and
        axiom, carried as data (`beschraenktPreis`,
        `fluechtigPreis`), never proved.
    C5  The admissions stay TEMPLATE rulings semantically: Lean
        proves each named shape is tabled, not that its price is
        adequate. Each named shape still owes its one-by-one
        semantic decision; adequacy stays owed per slot.
    C6  The rechecker (§10) is DRAFT, no `theorem`: the bridges
        from its legs to the sentences, and the second program
        that reads the run artefacts, stand outside this file.
    C7  The five priced slots (§11) carry price as DATA; Lean
        proves nothing about price adequacy. `tafel` itself is
        frozen except status-field decisions.

   Premises (trusted, not proved):
     P1  The 19 `CForm` shapes are the named target language (`Ziel.lean`).
     P2  Each Gabbro primitive lowers to at most `proPrimitiv` C statements
         (`Absenkung`; the measured bound is 17 -- see `Ziel.lean` and
         `messung/ABSENKUNG-MESSUNG.md`).
     P3  The census counts are faithful (`zaehle-c-formen.py`: 64 forms,
         30 undecided census slots, 491 pointer-arithmetic sites).

   No `mathlib`, no `sorry`, no `admit`, no `axiom`, and no new axiom
   introduced: `#print axioms` at the end names all standard axioms the
   new theorems rest on.
-/
module

public import Grammatik.Kern.Semantik.Erhaltung.Teil1
public import Grammatik.Kern.Semantik.Erhaltung.Teil2
