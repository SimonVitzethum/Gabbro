/-
  File:       Grammatik/Erhaltung.lean
  Subject:    The PRODUCER CONTRACT as specification: what the emitter must
              uphold, written as Lean shapes. Design only.

  Claim (in one sentence):
    The emitter earns trust per run through a correspondence certificate
    (every Gabbro evaluation site exactly once, in order, over ruled forms
    only, with no C site lacking a Gabbro preimage), through an alias
    obligation (no address arithmetic in the image, the 491 census sites
    named), and through a cost obligation (CerCo preserves the ops count,
    the production compiler is only measured by witness pairs) -- and the
    per-form ruling table below names all 49 slots with their status, the
    `?:` ruling as the filled template.

  Mapping to the measured base (read-only, not imported as code):
    `Ziel.lean` `CForm`/`Absenkung` -- the 19 named shapes this table rules on,
      and the bounded lowering the cost shape rests on.
    `dokumente/BEWEIS.md` Gegenstand 2 -- the census (64 forms over 8001
      lines: 34 allowed-and-used, 30 undecided), the two rulings (`?:`,
      `__builtin_unreachable`), the UB inventory rows 2/5/11/12, and the
      per-run coverage certificate (§4: completeness, order, closure,
      no additional effect).
    `dokumente/SYNTAX.md` §18 -- the closed-list sentence this file turns
      into data; the prose for the new §19 stands in
      `messung/SYNTAX-ERHALTUNG-ENTWURF.md` (this lane does NOT edit it).

   Proved here (this lane): the Lean-side legs of the emitter contract --
     correspondence VALIDATION (a Boolean recomputation over the certificate
     whose success IMPLIES the four correspondence sentences, §6), the alias
     discharge shape (`aliasKept` from the empty site list, §7), and the cost
     legs (CerCo preservation as an implication, production measurement as
     an implication, bounded lowering from the measured bound, §8). The shape
     mirrors the `Zeugnis.lean` soundness pattern: recompute, then `decide`.
     Every theorem ends with a `#print axioms` line: Lean's standard axioms
     (`propext`, `Quot.sound`) only.

   Shapes that stay unproved (booked cuts, not faked): the recomputer that
     would PRODUCE a valid certificate (needs the second program), what a C
     form MEANS (witness-pair execution, C semantics), and with them the 28
     open slots -- `tafel_nicht_geschlossen` (§9) proves the debt is real,
     and `vertrag_braucht_tafel` proves the contract does not hold today.
     `satz_tafel` and `satz_erzeugervertrag` stay SPECIFICATION.

  Premises (trusted, not proved):
    P1  The 19 `CForm` shapes are the named target language (`Ziel.lean`).
    P2  Each Gabbro primitive lowers to at most `proPrimitiv` C statements
        (`Absenkung`; the number 4 is itself unmeasured -- see `Ziel.lean`).
    P3  The census counts are faithful (`zaehle-c-formen.py`, 2026-08-31:
        64 forms, 30 undecided, 491 pointer-arithmetic sites).

   Cuts (rebooked 2026-09-10: shrunk, not faked):
      C1  CLOSED (2026-09-11, p17): `korrespondenz_sound` still proves
          valid-cert-implies-correspondence, but the correspondence now NAMES
          its image -- `emittedMarker` is the word `emit.rs` (`emittiere_mit`)
          writes beside each emitted site, `emittedRowFields`/`cformWort`
          mirror the certificate rows witnessed by
          `messung/proben/corrcert/korr-*.json`, and `markerStimmtB` rechecks
          marker-vs-row agreement (§6b). Lean still PRODUCES no certificate;
          the second program stays `instrumente/nachpruefer.py`.
     C2  What a C form MEANS stays cut: `geschlossen_immer` proves every
         named shape IS tabled (closure holds unconditionally), but the
         meaning still rides on the hand-written table entry plus its
         executable witness pair, and the common-mode failure (both tables
         from one text) is named, not closed.
     C3  `restrict` and `volatile` stay trust: priced option and axiom,
         carried as data (`beschraenktPreis`, `fluechtigPreis`), never
         proved.
     C4  COVERED (was: not wired into `Grammatik.lean`): `Grammatik.lean`
         imports this file, so `lake build` checks it; after a build the
         single-file check `lake env lean Grammatik/Erhaltung.lean` holds too.
     C5  The 19 admissions stay TEMPLATE rulings semantically: Lean proves
         each named shape is tabled (`ruledB_voll`), not that its price is
         adequate. Each named shape still owes its one-by-one semantic
          decision the way `?:` got its (`bedingtEntscheid`); the 28 open
          slots are proved debt (`tafel_nicht_geschlossen`), countable via
          the status field. Lane 121 flips four of them in `tafel` itself
          (`zeigerIndex`, `abbruchStmt`, `logUndOder`, `fortStmt`, each row
          citing its `messung/CFORM-REGEL-*.md` ruling); adequacy still owed
          per slot, the debt proof now rests on the remaining open rows.
          Lane p06 flips three C2 rows in `tafel` itself (`voidTyp`,
          `cAttribut`, `cSizeof`, each row citing its
          `messung/CFORM-REGEL-*.md` ruling); five C1 rows remain open.
      C6  Der Nachpruefer bleibt Schnitt: `nachpruefer` (§10) rechnet
          Laufartefakte (Gabbro-Stellen, Zertifikat, Aliaslast, Kostenaussage,
          Paare, Anweisungszahl) zu einem Urteil nach, und
          `satz_nachpruefung_vertrauen` nennt die Gestalt der Verknuepfung
          (gueltiges Urteil heisst vertrauenswuerdiges Zertifikat). Die Gestalt
          ist ENTWURF, kein Satz: kein `theorem`-Befehl in dieser Bahn, und das
          zweite Programm, das die Artefakte aus dem Lauf liest, steht nicht
          hier (Klasse von C1).
      C7  Die fuenf bepreisten Stellen bleiben Schablonen dem Sinn nach:
          `tafelNeu` (§11) traegt `bedingt`, `logUndOder`, `fortStmt`,
          `abbruchStmt` und `zeigerIndex` mit Preis im Statusfeld, sonst
          unveraendert aus `tafel` nachgerechnet. Lean beweist damit nichts
          ueber die Angemessenheit eines Preises (C5 gilt weiter); `tafel`
          selbst bleibt eingefroren, und `satz_tafel` spricht weiter von ihr.
          Bahn 121: `tafel` traegt die vier Zulassungen seither unmittelbar
          (Statusfeld entschieden mit Preis, je Zeile mit Regelnotiz belegt);
          `tafelNeu` rechnet denselben Stand nach. Eingefroren heisst seither:
          nur Statusfeld-Entscheidungen, sonst keine Aenderung.

   No `mathlib`, no `sorry`, no `admit`, no `axiom`, and no new axiom
     introduced: `#print axioms` at the end names all standard axioms the
     new theorems rest on.

  No `mathlib`, no `sorry`, no `admit`, no `axiom`.
-/
import Grammatik.Ziel

namespace Gabbro.Grammatik

/-! ## 1. Correspondence: exec-to-C, as data plus four Prop shapes -/

/-- One evaluation site on each side, joined by its form: the row of the
    per-run coverage certificate (`BEWEIS.md` §4). Sites are `Nat` ids;
    binding them to source spans is the recomputer's job (cut C1). -/
structure CorrSite where
  gabbroSite : Nat
  cSite : Nat
  form : CForm
  deriving DecidableEq, Repr

/-- The per-run certificate: the list of joined sites. -/
structure CorrCert where
  sites : List CorrSite
  deriving DecidableEq, Repr

/-- §4.1 Completeness: every Gabbro evaluation site appears at least once. -/
def corrComplete (gabbroSites : List Nat) (cert : CorrCert) : Prop :=
  ∀ g ∈ gabbroSites, ∃ s ∈ cert.sites, s.gabbroSite = g

/-- §4.2 Order: the C sites stand in the same order as the certificate. -/
def corrOrdered (cert : CorrCert) : Prop :=
  cert.sites.Pairwise fun a b => a.cSite ≤ b.cSite

/-- §4.3 Closure: every C form in the image stands in the ruled list.
    What "ruled" means is the table of §4 below (`entschieden`). -/
def corrClosed (cert : CorrCert) (ruled : CForm → Prop) : Prop :=
  ∀ s ∈ cert.sites, ruled s.form

/-- §4.4 No additional effect: no C site without a Gabbro preimage. -/
def corrNoExtra (gabbroSites : List Nat) (cert : CorrCert) : Prop :=
  ∀ s ∈ cert.sites, s.gabbroSite ∈ gabbroSites

/-! ## 2. Alias: no address arithmetic in the image, sites named -/

/-- The census number this obligation answers (`BEWEIS.md` C1, §2 row 2):
    491 `d->basis + 8` / `v->bytes + 4` sites against a row that promised
    none. Kept as data so the draft §19 can quote it, not as prose. -/
def ptrArithCensus : Nat := 491

/-- The two declaration shapes the 491 sites compute on: `basis` is
    `volatile uint8_t *`, `bytes` is `uint8_t *`. -/
inductive ArithSource where
  | basisPlus
  | bytesPlus
  deriving DecidableEq, Repr

/-- The obligation: the image carries its address-arithmetic sites openly.
    Fulfilled exactly when the list is empty; until then every entry is a
    named site id, not a residual risk of "none". -/
structure AliasObligation where
  arithSites : List Nat
  deriving DecidableEq, Repr

/-- Alias preserved: no address-arithmetic site in this image. -/
def aliasKept (o : AliasObligation) : Prop :=
  o.arithSites = []

/-! ## 3. Cost: CerCo preserves, production is measured -- as data -/

/-- Who carries the ops count from C to Asm. The distinction is DATA, not
    prose: only the `cerCo` carrier may be CLAIMED to preserve; the
    production compiler's count is MEASURED by witness pairs (`BEWEIS.md`
    §1b pattern), never proved here. -/
inductive CostCarrier where
  | cerCo
  | produktion
  deriving DecidableEq, Repr

/-- The cost claim of one compilation run: both counts plus who carries. -/
structure CostClaim where
  carrier : CostCarrier
  opsGabbro : Nat
  opsC : Nat
  deriving DecidableEq, Repr

/-- Cost preserved: under the CerCo carrier the C count IS the Gabbro
    count. For `produktion` this says nothing (it is the measured leg). -/
def costKept (k : CostClaim) : Prop :=
  k.carrier = .cerCo → k.opsC = k.opsGabbro

/-- Cost measured: under the production carrier, `paare` witness pairs ran
    green for this run. Zero pairs is not a measurement. -/
def costMeasured (k : CostClaim) (paare : Nat) : Prop :=
  k.carrier = .produktion → 0 < paare

/-- The lowering leg on the Gabbro side: one primitive becomes at most
    `proPrimitiv` C statements (premise P2, `Absenkung`). -/
def senkungBegrenzt (a : Absenkung) (cAnweisungen : Nat) : Prop :=
  cAnweisungen ≤ a.proPrimitiv

/-! ## 4. The ruling table: 19 named shapes, 30 census slots, one status -/

/-- The status every slot carries. `aufListe` names the PRICE of the form's
    semantics; `ausErzeuger` names the REPLACEMENT the generator writes
    instead. `offen` is countable debt, not a shrug. -/
inductive RulingStatus where
  | offen
  | aufListe (preis : String)
  | ausErzeuger (ersatz : String)
  deriving DecidableEq, Repr

/-- The 30 census slots (`BEWEIS.md` §1a: C1 = 7, C2 = 19, C3 = 4).
    Each doc line carries its site count, so the table quotes the census
    instead of restating it. -/
inductive OffeneForm where
  | zeigerArithmetik   -- C1: 491 sites; contradicts §2 row 2 as written
  | zeigerIndex        -- C1: 156 sites; `p[i]` IS `*(p+i)` by C's definition
  | cInclude           -- C1: 408 sites; preprocessor other than `#if`
  | cTypedef           -- C1: 240 sites; the list says typedef-free
  | cDefine            -- C1: 210 sites; "enum-free constants" plainly means it
  | cEnum              -- C1: 28 sites; the list says enum-free
  | bedingt            -- C1: 8 sites; RULED, the filled template below
  | voidTyp            -- C2: 930 sites; the type row never names it
  | cAttribut          -- C2: 766 sites
  | cInline            -- C2: 440 sites
  | cConst             -- C2: 419 sites
  | deref              -- C2: 141 sites
  | adressVon          -- C2: 111 sites
  | bitNicht           -- C2: 98 sites
  | abbruchStmt        -- C2: 51 sites (`break`)
  | schrittStmt        -- C2: 42 sites (`++`/`--`)
  | cSizeof            -- C2: 27 sites
  | logUndOder         -- C2: 23 sites; conditional like `?:`, second door
  | doubleTyp          -- C2: 18 sites; no float row at all, third door with `floatTyp`
  | schleifeStmt       -- C2: 11 sites (`while`)
  | typOfErw           -- C2: 9 sites (`__typeof__`)
  | floatTyp           -- C2: 8 sites; no float row at all
  | unerreichbarBuiltin-- C2: 5 sites; RULED once, kept at one site (`BEWEIS.md` §1b)
  | wennGnuC           -- C2: 5 sites; `#if defined(__GNUC__)` changes the program per compiler
  | fortStmt           -- C2: 3 sites (`continue`)
  | statikAssert       -- C2: 1 site (`_Static_assert`)
  | pfeilZugriff       -- C3: 704 sites; generous reading of "field access"
  | boolTyp            -- C3: 350 sites; `<stdbool.h>` for `_Bool`
  | boolLit            -- C3: 211 sites (`true`/`false`)
  | zusammZuweisung    -- C3: 24 sites; generous reading of "assignment"
  deriving DecidableEq, Repr

/-- The filled template: the `?:` ruling the way every slot must be ruled.
    Generator wrong, not the list: all 8 sites are one line out of one
    emission site, and `if (v > z) { z = v; }` costs nothing at any level
    (`-O0`: 34 vs 34; `-O2`/`-Os`: byte-identical). The class stays open:
    `logUndOder` is the same conditional door, undecided. -/
def bedingtEntscheid : RulingStatus :=
  .ausErzeuger "if (v > z) { z = v; }"

/-- One row of the obligation table: either a named shape or a census
    slot, each WITH its status. The status field is what makes 30 holes
    countable instead of invisible. -/
inductive EntscheidZiel where
  | benannt (f : CForm) (s : RulingStatus)
  | luecke (u : OffeneForm) (s : RulingStatus)
  deriving DecidableEq, Repr

/-- Price of `beschraenkt` (`restrict`): a proof export into C's UB rules
    (`BEWEIS.md` row 11) -- priced option, never default (cut C3). -/
def beschraenktPreis : String :=
  "exports the effects-promise into C UB rules; only where the benchmark buys it"

/-- Price of `fluechtig` (`volatile`): weakly specified, MMIO practice --
    an axiom by name (cut C3). -/
def fluechtigPreis : String :=
  "axiom, named; seL4 excludes exactly this"

/-- The table: the 19 named shapes admitted with their price (template
    admissions per cut C5), the 30 census slots open -- except `bedingt`,
    which carries the filled template. -/
def tafel : List EntscheidZiel :=
  [.benannt .statisch (.aufListe "declaration header; no semantics beyond linkage"),
   .benannt .extern (.aufListe "foreign body; the null-spelling boundary lives here"),
   .benannt .zuweisung (.aufListe "E2: assignment is not an expression, one effect per statement"),
   .benannt .wenn (.aufListe "two-sided branch; no fall-through"),
   .benannt .schalter (.aufListe "exhaustive switch, no default"),
   .benannt .zaehlSchleife (.aufListe "counting loop over a bounded range"),
   .benannt .rueckgabe (.aufListe "single return of the declared type"),
   .benannt .sprungAlsSchleifenende (.aufListe "goto ONLY as a generated loop exit; counted, target unchecked"),
   .benannt .ruf (.aufListe "call to a declared or foreign body"),
   .benannt .literal (.aufListe "constant of a named type"),
   .benannt .name (.aufListe "identifier read; no implicit conversion at the read"),
   .benannt .feld (.aufListe "field access; padding bytes never read"),
   .benannt .index (.aufListe "index over the declared range; pointer-index is NOT this (see zeigerIndex)"),
   .benannt .wahlLesen (.aufListe "conditional read with the condition evaluated once"),
   .benannt .atomar (.aufListe "named ordering; orders under A10"),
   .benannt .beschraenkt (.aufListe beschraenktPreis),
   .benannt .fluechtig (.aufListe fluechtigPreis),
   .benannt .noreturn (.aufListe "proven non-return; the fall-through export needs D005 plus the tag invariant"),
   .benannt .asmEins (.aufListe "exactly one emission site; no downstream prover (16.2 (7))"),
   .luecke .zeigerArithmetik (.aufListe "no computed address outside place[expr]; unproven bound refused"),  -- ruled: SPRACHE.md 5.2 + lane 142, re-decided over the scoped emitter map (withdrawn same-day on the unscoped one)
   .luecke .zeigerIndex (.aufListe "Adressrechnung; Pflicht je Stelle, in den Grenzen zu bleiben; UB-Zeile fuer den Aussenfall"),  -- ruled: messung/CFORM-REGEL-ZEIGERINDEX.md
   .luecke .cInclude .offen,
    .luecke .cTypedef (.aufListe "alias only; layout fixed once; unique names"),  -- ruled: messung/CFORM-REGEL-TYPEDEF.md
    .luecke .cDefine (.aufListe "object-like macro only; typed reads"),  -- ruled: messung/CFORM-REGEL-DEFINE.md
    .luecke .cEnum (.aufListe "closed alternative list as int"),  -- ruled: messung/CFORM-REGEL-ENUM.md
   .luecke .bedingt bedingtEntscheid,
   .luecke .voidTyp (.aufListe "empty result and parameter types as types; silence casts as deliberate"),  -- ruled: messung/CFORM-REGEL-VOID.md
   .luecke .cAttribut (.aufListe "truthful unused statement; checked pure/const effect promise; two-name section promise"),  -- ruled: messung/CFORM-REGEL-ATTRIBUT.md
   .luecke .cInline (.aufListe "non-binding inline request"),  -- ruled: messung/CFORM-REGEL-INLINE.md
   .luecke .cConst (.aufListe "read-only qualifier"),  -- ruled: messung/CFORM-REGEL-CONST.md
   .luecke .deref (.aufListe "plain dereference"),  -- ruled: messung/CFORM-REGEL-DEREF.md
   .luecke .adressVon (.aufListe "provenance-carrying address"),  -- ruled: messung/CFORM-REGEL-ADRESSE.md
   .luecke .bitNicht (.aufListe "double-cast width rule"),  -- ruled: messung/CFORM-REGEL-TILDE.md
   .luecke .abbruchStmt (.aufListe "Austritt aus dem Laufenskelett und Abschluss der Fallarme aus je zwei Emissionszeilen; kein Nutzerpfad; kein UB"),  -- ruled: messung/CFORM-REGEL-BREAK.md
   .luecke .schrittStmt (.aufListe "++ to += 1; exchange CAS untouched"),  -- ruled: messung/CFORM-REGEL-SENKUNG-142.md + ZULASSUNG-143 batch
   .luecke .cSizeof (.aufListe "layout-derived compile-time count; operands never evaluated"),  -- ruled: messung/CFORM-REGEL-SIZEOF.md
   .luecke .logUndOder (.aufListe "bedingte Auswertung mit Sequenzpunkt; Ergebnis 0 oder 1; Klammerpflicht beim Erzeuger"),  -- ruled: messung/CFORM-REGEL-LOGUNDODER.md
   .luecke .doubleTyp (.aufListe "f64 to double lowered; mixed-width refused"),  -- ruled: messung/CFORM-REGEL-SENKUNG-142.md + SENKUNG-144
   .luecke .schleifeStmt (.aufListe "retry skeleton only"),  -- ruled: messung/CFORM-REGEL-SENKUNG-142.md + SENKUNG-144
   .luecke .typOfErw (.aufListe "checked reference, single source"),  -- ruled: messung/CFORM-REGEL-SENKUNG-142.md + SENKUNG-144
   .luecke .floatTyp (.aufListe "f32 to float with suffix"),  -- ruled: messung/CFORM-REGEL-SENKUNG-144.md
   .luecke .unerreichbarBuiltin (.aufListe "kept at one site: D005 plus the tag invariant; four deletable sites out of the generator"),
   .luecke .wennGnuC (.aufListe "guard fires exactly when all arms return"),  -- ruled: messung/CFORM-REGEL-SENKUNG-144.md
   .luecke .fortStmt (.aufListe "Steuerung des Laufenskeletts aus einer Emissionszeile; kein Nutzerpfad; kein UB"),  -- ruled: messung/CFORM-REGEL-CONTINUE.md
   .luecke .statikAssert (.aufListe "declared spaces keep the assert"),  -- ruled: messung/CFORM-REGEL-SENKUNG-144.md
   .luecke .pfeilZugriff (.aufListe "generous reading of field access"),
   .luecke .boolTyp (.aufListe "generous reading: <stdbool.h> for _Bool"),
   .luecke .boolLit (.aufListe "generous reading: boolean literals"),
   .luecke .zusammZuweisung (.aufListe "generous reading of assignment")]

/-- Decided: a named shape always counts as tabled; a slot counts exactly
    when its status stopped being `offen`. -/
def entschieden : EntscheidZiel → Prop
  | .benannt _ _ => True
  | .luecke _ .offen => False
  | .luecke _ _ => True

/-! ## 5. The sentences for later -- shapes only, no claims -/

/-- Later sentence 1 (correspondence): this run's certificate is complete,
    ordered, closed over the decided forms, and adds no effect. -/
def satz_korrespondenz (gabbroSites : List Nat) (cert : CorrCert) : Prop :=
  corrComplete gabbroSites cert ∧ corrOrdered cert ∧
    corrClosed cert (fun f => ∃ s : RulingStatus, .benannt f s ∈ tafel ∧ entschieden (.benannt f s)) ∧
    corrNoExtra gabbroSites cert

/-- Later sentence 2 (alias): this image carries no address arithmetic.
    Today `⟨List.replicate ptrArithCensus 0⟩` would be the honest witness,
    not the empty list -- the shape says which one the proof must take. -/
def satz_alias (o : AliasObligation) : Prop :=
  aliasKept o

/-- Later sentence 3 (cost): the CerCo leg preserves, the production leg
    is measured by `paare` pairs, and the lowering leg stays bounded. -/
def satz_kosten (k : CostClaim) (paare : Nat) (a : Absenkung) (cAnweisungen : Nat) : Prop :=
  costKept k ∧ costMeasured k paare ∧ senkungBegrenzt a cAnweisungen

/-- Later sentence 4 (table): every row of the table is decided. This is
    FALSE today (28 slots still `offen`) -- and that is the point: the
    shape counts the debt instead of hiding it. -/
def satz_tafel : Prop :=
  ∀ e ∈ tafel, entschieden e

/-- Later sentence 5 (the contract): correspondence, alias, cost, and the
    decided table, conjoined -- the SPECIFICATION the emitter must uphold,
    as one shape. -/
def satz_erzeugervertrag (gabbroSites : List Nat) (cert : CorrCert)
    (o : AliasObligation) (k : CostClaim) (paare : Nat)
    (a : Absenkung) (cAnweisungen : Nat) : Prop :=
  satz_korrespondenz gabbroSites cert ∧ satz_alias o ∧
    satz_kosten k paare a cAnweisungen ∧ satz_tafel

/-! ## 6. Correspondence, Lean side: recompute, then `decide` -/

/-- Recompute 1/4 (completeness, §4.1): every Gabbro site has a joined row.
    Boolean mirror of `corrComplete`, so a run's certificate can be CHECKED
    instead of believed. -/
def vollB (gabbroSites : List Nat) (cert : CorrCert) : Bool :=
  gabbroSites.all fun g => cert.sites.any fun s => decide (s.gabbroSite = g)

/-- Soundness 1/4: a successful recomputation IMPLIES completeness. -/
theorem vollB_sound (gabbroSites : List Nat) (cert : CorrCert)
    (h : vollB gabbroSites cert = true) : corrComplete gabbroSites cert := by
  have h' : gabbroSites.all (fun g => cert.sites.any fun s => decide (s.gabbroSite = g)) = true := by
    simpa only [vollB] using h
  have hall := List.all_eq_true.mp h'
  intro g hg
  have hmem := hall g hg
  have hex := List.any_eq_true.mp hmem
  obtain ⟨s, hs, heq⟩ := hex
  exact ⟨s, hs, of_decide_eq_true heq⟩

/-- Recompute 4/4 (no additional effect, §4.4): every row has a preimage. -/
def ohneExtraB (gabbroSites : List Nat) (cert : CorrCert) : Bool :=
  cert.sites.all fun s => decide (s.gabbroSite ∈ gabbroSites)

/-- Soundness 4/4: a successful recomputation IMPLIES no additional effect. -/
theorem ohneExtraB_sound (gabbroSites : List Nat) (cert : CorrCert)
    (h : ohneExtraB gabbroSites cert = true) : corrNoExtra gabbroSites cert := by
  have h' : cert.sites.all (fun s => decide (s.gabbroSite ∈ gabbroSites)) = true := by
    simpa only [ohneExtraB] using h
  have hall := List.all_eq_true.mp h'
  intro s hs
  exact of_decide_eq_true (hall s hs)

/-- Recompute 2/4 (order, §4.2) over the C-site ids. Adjacent check only;
    transitivity (`Nat.le_trans`) lifts it to every pair (`geordnetB_hilf`). -/
def geordnetB : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => if a ≤ b then geordnetB (b :: rest) else false

/-- The lift: a passing adjacent check bounds every later element. -/
theorem geordnetB_hilf : ∀ (l : List Nat) (a : Nat),
    geordnetB (a :: l) = true → ∀ y ∈ l, a ≤ y
  | [], _, _, y, hy => False.elim (List.not_mem_nil hy)
  | b :: rest, a, h, y, hy => by
    simp only [geordnetB] at h
    by_cases hab : a ≤ b
    · rw [if_pos hab] at h
      simp only [List.mem_cons] at hy
      cases hy with
      | inl heq => rw [heq]; exact hab
      | inr hin =>
        have hby : b ≤ y := geordnetB_hilf rest b h y hin
        exact Nat.le_trans hab hby
    · rw [if_neg hab] at h
      contradiction

/-- Soundness 2/4: a successful recomputation IMPLIES the order. -/
theorem geordnet_sound : ∀ (l : List Nat), geordnetB l = true → l.Pairwise (· ≤ ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.Pairwise.cons (fun _ hx => False.elim (List.not_mem_nil hx)) List.Pairwise.nil
  | a :: b :: rest, h => by
    have hunfold : geordnetB (a :: b :: rest) = (if a ≤ b then geordnetB (b :: rest) else false) := by
      simp only [geordnetB]
    by_cases hab : a ≤ b
    · have hrest : geordnetB (b :: rest) = true := by
        rw [hunfold, if_pos hab] at h
        exact h
      exact List.Pairwise.cons (geordnetB_hilf (b :: rest) a h) (geordnet_sound (b :: rest) hrest)
    · rw [hunfold, if_neg hab] at h
      contradiction

/-- Order over the certificate: project the C sites, then recompute. -/
def geordnetCertB (cert : CorrCert) : Bool :=
  geordnetB (cert.sites.map CorrSite.cSite)

/-- The projection preserves the order statement (`List.pairwise_map`). -/
theorem geordnetCertB_sound (cert : CorrCert) (h : geordnetCertB cert = true) :
    corrOrdered cert := by
  have hp := geordnet_sound _ (by simpa only [geordnetCertB] using h)
  have hm := List.pairwise_map.mp hp
  simpa only [corrOrdered] using hm

/-- Recompute 3/4 (closure, §4.3): the form's row is in the table. -/
def ruledB (f : CForm) : Bool :=
  tafel.any fun e => match e with
    | .benannt g _ => decide (g = f)
    | .luecke _ _ => false

/-- Soundness 3/4: a found row IS a decided table entry. -/
theorem ruledB_sound (f : CForm) (h : ruledB f = true) :
    ∃ s : RulingStatus, .benannt f s ∈ tafel ∧ entschieden (.benannt f s) := by
  have hex := List.any_eq_true.mp (by simpa only [ruledB] using h)
  obtain ⟨e, he, hb⟩ := hex
  cases e with
  | benannt g s =>
    have hgf : g = f := of_decide_eq_true hb
    subst hgf
    exact ⟨s, he, trivial⟩
  | luecke _ _ =>
    contradiction

/-- Every named shape has its row: all 19, one by one, each by `decide`. -/
theorem ruledB_voll : ∀ f, ruledB f = true := by
  intro f
  cases f <;> decide

/-- Closure over the certificate, from the row check. -/
def geschlossenB (cert : CorrCert) : Bool :=
  cert.sites.all fun s => ruledB s.form

/-- Soundness 3/4 over the certificate. -/
theorem geschlossenB_sound (cert : CorrCert) (h : geschlossenB cert = true) :
    corrClosed cert (fun f => ∃ s : RulingStatus, .benannt f s ∈ tafel ∧ entschieden (.benannt f s)) := by
  have h' : cert.sites.all (fun s => ruledB s.form) = true := by
    simpa only [geschlossenB] using h
  have hall := List.all_eq_true.mp h'
  intro s hs
  exact ruledB_sound _ (hall s hs)

/-- Closure holds for EVERY certificate: each of the 19 named shapes is
    tabled, so no image can fall outside the ruled list. (The SEMANTIC
    ruling -- what the row means -- stays cut C2.) -/
theorem geschlossen_immer (cert : CorrCert) :
    corrClosed cert (fun f => ∃ s : RulingStatus, .benannt f s ∈ tafel ∧ entschieden (.benannt f s)) :=
  geschlossenB_sound cert (List.all_eq_true.mpr (fun s _ => ruledB_voll s.form))

/-- Four passing legs ASSEMBLE the correspondence sentence. -/
theorem korrespondenz_aus_vieren (gabbroSites : List Nat) (cert : CorrCert)
    (hv : vollB gabbroSites cert = true) (hg : geschlossenB cert = true)
    (hn : ohneExtraB gabbroSites cert = true) (ho : geordnetCertB cert = true) :
    satz_korrespondenz gabbroSites cert :=
  ⟨vollB_sound _ _ hv, geordnetCertB_sound _ ho,
    geschlossenB_sound _ hg, ohneExtraB_sound _ _ hn⟩

/-- The per-run check, recomputed Lean-side: all four legs, right-nested so
    `Bool.and_eq_true_iff` splits it back into the four soundness premises. -/
def pruefeKorrespondenz (gabbroSites : List Nat) (cert : CorrCert) : Bool :=
  vollB gabbroSites cert && (geschlossenB cert && (ohneExtraB gabbroSites cert && geordnetCertB cert))

/-- Certificate validity: the recomputation SUCCEEDS. Decidable by
    construction, so acceptance and rejection both close by `decide` --
    the `Zeugnis.lean` (`GueltigAbleitung`) pattern. -/
abbrev GueltigKorrespondenz (gabbroSites : List Nat) (cert : CorrCert) : Prop :=
  pruefeKorrespondenz gabbroSites cert = true

/-- Soundness: a valid certificate IMPLIES the correspondence sentence.
    This file's direction, mirroring `zeugnis_sound`: the recomputer that
    would PRODUCE such a certificate stays cut (C1). -/
theorem korrespondenz_sound (gabbroSites : List Nat) (cert : CorrCert)
    (h : GueltigKorrespondenz gabbroSites cert) : satz_korrespondenz gabbroSites cert := by
  have hval : pruefeKorrespondenz gabbroSites cert = true := h
  have h4 : vollB gabbroSites cert = true ∧ geschlossenB cert = true ∧
      ohneExtraB gabbroSites cert = true ∧ geordnetCertB cert = true := by
    simpa only [pruefeKorrespondenz, Bool.and_eq_true_iff] using hval
  exact korrespondenz_aus_vieren _ _ h4.1 h4.2.1 h4.2.2.1 h4.2.2.2

/-- Accept: two sites, in order, over named forms, nothing more. -/
example : GueltigKorrespondenz [0, 1]
    ⟨[{gabbroSite := 0, cSite := 0, form := .literal},
      {gabbroSite := 1, cSite := 1, form := .name}]⟩ := by decide

/-- Reject: Gabbro site 1 has no row (completeness fails loudly). -/
example : ¬ GueltigKorrespondenz [0, 1]
    ⟨[{gabbroSite := 0, cSite := 0, form := .literal}]⟩ := by decide

/-- Reject: the C sites run backwards (order fails loudly). -/
example : ¬ GueltigKorrespondenz [0, 1]
    ⟨[{gabbroSite := 0, cSite := 1, form := .literal},
      {gabbroSite := 1, cSite := 0, form := .name}]⟩ := by decide

/-- Reject: a C site without a Gabbro preimage (no-extra fails loudly). -/
example : ¬ GueltigKorrespondenz [0]
    ⟨[{gabbroSite := 0, cSite := 0, form := .literal},
      {gabbroSite := 5, cSite := 1, form := .name}]⟩ := by decide

/-- End to end: a valid certificate YIELDS the correspondence sentence. -/
example : satz_korrespondenz [0, 1]
    ⟨[{gabbroSite := 0, cSite := 0, form := .literal},
      {gabbroSite := 1, cSite := 1, form := .name}]⟩ :=
  korrespondenz_sound _ _ (by decide)

/-- The empty run corresponds, vacuously: no site owes a row. -/
theorem korrespondenz_leer : satz_korrespondenz [] ⟨[]⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg
    exact False.elim (List.not_mem_nil hg)
  · exact List.Pairwise.nil
  · intro s hs
    exact False.elim (List.not_mem_nil hs)
  · intro s hs
    exact False.elim (List.not_mem_nil hs)

/-! ## 6b. The emitted witness: the C1 correspondence names its image -/

/-- The word the emitter writes into the image beside each emitted evaluation
    site (`crates/gabbro-check/src/emit.rs`, `emittiere_mit`, as the comment
    `/* gabbro-site <cSite> <form> */`). Naming the word is the C1 closure
    Lean-side: the recomputer (`instrumente/nachpruefer.py`) reads exactly
    this marker back. -/
def emittedMarker : String := "gabbro-site"

/-- The JSON field names of one certificate row, as the emitter writes them
    beside the C output (`CorrCert::to_json` in
    `crates/gabbro-check/src/corrcert.rs`). Machine-readable witness:
    `messung/proben/corrcert/korr-*.json` carry these names word for word. -/
def emittedRowFields : List String :=
  ["gabbroSite", "cSite", "form"]

/-- The word of one target shape: the `form` value a certificate row carries.
    Mirrors `CForm::as_str` in `crates/gabbro-check/src/corrcert.rs` one for
    one, so Lean rows, certificate JSON, and image markers spell every form
    with one word. -/
def cformWort : CForm → String
  | .statisch => "statisch"
  | .extern => "extern"
  | .zuweisung => "zuweisung"
  | .wenn => "wenn"
  | .schalter => "schalter"
  | .zaehlSchleife => "zaehlSchleife"
  | .rueckgabe => "rueckgabe"
  | .sprungAlsSchleifenende => "sprungAlsSchleifenende"
  | .ruf => "ruf"
  | .literal => "literal"
  | .name => "name"
  | .feld => "feld"
  | .index => "index"
  | .wahlLesen => "wahlLesen"
  | .atomar => "atomar"
  | .beschraenkt => "beschraenkt"
  | .fluechtig => "fluechtig"
  | .noreturn => "noreturn"
  | .asmEins => "asmEins"

/-- Marker agreement (the image direction of no-extra): every marked C site
    owns a certificate row in the same form word. The cert-only direction
    (`ohneExtraB`: every row has a preimage) cannot see an effect the image
    names but no row claims; this Boolean is what the recomputer checks the
    emitted construct against. -/
def markerStimmtB (cert : CorrCert) (marken : List (Nat × String)) : Bool :=
  marken.all fun m => cert.sites.any fun s =>
    decide (s.cSite = m.1) && decide (cformWort s.form = m.2)

/-- Accept: the marked image agrees with its rows, word for word. -/
example : markerStimmtB
    ⟨[{gabbroSite := 0, cSite := 0, form := .literal},
      {gabbroSite := 1, cSite := 1, form := .name}]⟩
    [(0, "literal"), (1, "name")] = true := by decide

/-- Reject: the image marks C site 0 `name`, the row says `literal`. -/
example : markerStimmtB
    ⟨[{gabbroSite := 0, cSite := 0, form := .literal}]⟩
    [(0, "name")] = false := by decide

/-! ## 7. Alias, Lean side: the dischargeable shape -/

/-- `aliasKept` is decidable: the obligation is CHECKABLE per image. -/
instance aliasKeptDec (o : AliasObligation) : Decidable (aliasKept o) :=
  inferInstanceAs (Decidable (o.arithSites = []))

/-- Discharge: the empty site list keeps the obligation, by `rfl`. -/
theorem alias_leer : aliasKept { arithSites := [] } := rfl

/-- The census stands as data: 491 named sites (`BEWEIS.md` C1, §2 row 2). -/
theorem census_steht : ptrArithCensus = 491 := rfl

/-- Accept: no address-arithmetic site in this image. -/
example : aliasKept ⟨[]⟩ := by decide

/-- Reject: one named site breaks the obligation. -/
example : ¬ aliasKept ⟨[0]⟩ := by decide

/-- Reject, honestly: today's image carries the whole census, not the empty
    list -- `⟨List.replicate ptrArithCensus 0⟩` is the witness the proof must
    one day TAKE, and it does not discharge. -/
example : ¬ aliasKept ⟨List.replicate ptrArithCensus 0⟩ := by decide

/-! ## 8. Cost, Lean side: who may claim, who must measure -/

/-- Both cost claims are decidable: per-run CHECKS, not prose. -/
instance costKeptDec (k : CostClaim) : Decidable (costKept k) :=
  inferInstanceAs (Decidable (k.carrier = .cerCo → k.opsC = k.opsGabbro))

instance costMeasuredDec (k : CostClaim) (paare : Nat) : Decidable (costMeasured k paare) :=
  inferInstanceAs (Decidable (k.carrier = .produktion → 0 < paare))

instance senkungDec (a : Absenkung) (n : Nat) : Decidable (senkungBegrenzt a n) :=
  inferInstanceAs (Decidable (n ≤ a.proPrimitiv))

/-- CerCo leg: under the CerCo carrier, equal counts ARE preservation. -/
theorem kosten_cerCo_gilt (k : CostClaim) (_hc : k.carrier = .cerCo)
    (heq : k.opsC = k.opsGabbro) : costKept k := by
  intro _
  exact heq

/-- Production leg, first half: under the production carrier `costKept`
    claims NOTHING -- diverging counts still satisfy it, vacuously. -/
theorem kosten_produktion_frei (k : CostClaim) (hc : k.carrier = .produktion) :
    costKept k := by
  intro hcontra
  rw [hc] at hcontra
  contradiction

/-- Production leg, second half: a measurement needs a carrier AND a pair. -/
theorem gemessen_produktion (k : CostClaim) (paare : Nat)
    (_hc : k.carrier = .produktion) (hpos : 0 < paare) :
    costMeasured k paare := by
  intro _
  exact hpos

/-- CerCo side of the measurement: nothing to measure, vacuously true. -/
theorem gemessen_cerCo_frei (k : CostClaim) (paare : Nat)
    (hc : k.carrier = .cerCo) : costMeasured k paare := by
  intro hcontra
  rw [hc] at hcontra
  contradiction

/-- The carrier distinction IS the data: every claim picks a side. -/
theorem traeger_trennt (k : CostClaim) :
    k.carrier = .cerCo ∨ k.carrier = .produktion := by
  cases k.carrier with
  | cerCo => exact Or.inl rfl
  | produktion => exact Or.inr rfl

/-- Bounded lowering from the measured bound: 17 per primitive
    (`messung/ABSENKUNG-MESSUNG.md`), so anything under 17 stays under. -/
theorem senkung_aus_schranke (cAnweisungen : Nat) (h : cAnweisungen ≤ 17) :
    senkungBegrenzt absenkung cAnweisungen := h

/-- Assemble the cost sentence from its three legs. -/
theorem kosten_satz_bauen (k : CostClaim) (paare : Nat) (a : Absenkung)
    (cAnweisungen : Nat) (h1 : costKept k) (h2 : costMeasured k paare)
    (h3 : senkungBegrenzt a cAnweisungen) :
    satz_kosten k paare a cAnweisungen :=
  ⟨h1, h2, h3⟩

/-- CerCo with equal counts: kept. -/
example : costKept ⟨.cerCo, 4, 4⟩ := by decide

/-- Production with DIVERGING counts: still `costKept` -- the claim lives
    on the CerCo leg only, and this is the measured leg. -/
example : costKept ⟨.produktion, 4, 9⟩ := by decide

/-- CerCo with diverging counts: NOT kept. -/
example : ¬ costKept ⟨.cerCo, 4, 9⟩ := by decide

/-- Production with two green pairs: measured. -/
example : costMeasured ⟨.produktion, 4, 9⟩ 2 := by decide

/-- Production with zero pairs: not a measurement. -/
example : ¬ costMeasured ⟨.produktion, 4, 9⟩ 0 := by decide

/-- The bound, both directions, at the measured number. -/
example : senkungBegrenzt absenkung 17 := by decide
example : ¬ senkungBegrenzt absenkung 18 := by decide

/-! ## 9. What stays cut: the debt, proved real -/

/-- The table is NOT decided: `cInclude` stands open, with its row. -/
theorem tafel_nicht_geschlossen : ¬ satz_tafel := by
  intro h
  have hm : (.luecke .cInclude .offen : EntscheidZiel) ∈ tafel := by decide
  have hd := h _ hm
  exact hd

/-- The contract does not hold today: whatever the run proves, the table
    leg fails with it. `satz_erzeugervertrag` stays a SPECIFICATION. -/
theorem vertrag_braucht_tafel (gabbroSites : List Nat) (cert : CorrCert)
    (o : AliasObligation) (k : CostClaim) (paare : Nat)
    (a : Absenkung) (cAnweisungen : Nat) :
    ¬ satz_erzeugervertrag gabbroSites cert o k paare a cAnweisungen := by
  intro h
  exact tafel_nicht_geschlossen h.2.2.2

#print axioms Gabbro.Grammatik.entschieden
#print axioms Gabbro.Grammatik.satz_tafel
#print axioms Gabbro.Grammatik.satz_erzeugervertrag
#print axioms Gabbro.Grammatik.korrespondenz_sound
#print axioms Gabbro.Grammatik.geschlossen_immer
#print axioms Gabbro.Grammatik.ruledB_voll
#print axioms Gabbro.Grammatik.korrespondenz_leer
#print axioms Gabbro.Grammatik.alias_leer
#print axioms Gabbro.Grammatik.kosten_produktion_frei
#print axioms Gabbro.Grammatik.gemessen_produktion
#print axioms Gabbro.Grammatik.senkung_aus_schranke
#print axioms Gabbro.Grammatik.tafel_nicht_geschlossen
#print axioms Gabbro.Grammatik.vertrag_braucht_tafel

/-! ## 10. Der Nachpruefer als Programmgestalt: Laufartefakte hinein, Urteil hinaus -/

/-- Die Eingabe des Nachpruefers: alles, was ein Lauf hinterlaesst. Die
    Gabbro-Stellen und das Zertifikat kommen aus dem Erzeugnislauf, die
    Aliaslast aus dem Bild, die Kostenaussage mit ihren Paaren aus dem
    Messlauf, die Anweisungszahl aus der Absenkung. Das zweite Programm, das
    diese Artefakte aus dem Lauf liest, steht nicht hier (Schnitt C6). -/
structure NachprueferEingabe where
  gabbroSites : List Nat
  cert : CorrCert
  o : AliasObligation
  k : CostClaim
  paare : Nat
  cAnweisungen : Nat
  deriving DecidableEq, Repr

/-- Der Nachpruefer: alle Beine, nachgerechnet. Die Entsprechung ueber
    `pruefeKorrespondenz` (§6), die Aliaslast ueber die leere Stellenliste
    (§7), die Kostenaussage ueber ihre zwei Entscheidungsinstanzen (§8) und
    die Anweisungszahl ueber die gemessene Schranke 17. Ausgabe ist ein Urteil:
    `true` heisst angenommen. -/
def nachpruefer (eingabe : NachprueferEingabe) : Bool :=
  pruefeKorrespondenz eingabe.gabbroSites eingabe.cert &&
    (decide (eingabe.o.arithSites = []) &&
      (decide (costKept eingabe.k) &&
        (decide (costMeasured eingabe.k eingabe.paare) &&
          decide (eingabe.cAnweisungen ≤ 17))))

/-- Gueltigkeit: das nachgerechnete Urteil lautet angenommen. Entscheidbar aus
    Bauart, wie `GueltigKorrespondenz` -- Annahme und Ablehnung schliessen beide
    ueber die Nachrechnung, nicht ueber Glauben. -/
def nachprueferGueltig (eingabe : NachprueferEingabe) : Prop :=
  nachpruefer eingabe = true

/-- Die Verknuepfung zur Erzeugung, als Gestalt: ein gueltiges nachgerechnetes
    Urteil heisst, dem ausgestellten Zertifikat darf vertraut werden --
    Entsprechung ueber dem Lauf, Aliaslast getragen, Kosten gehalten und
    gemessen ueber `absenkung`. ENTWURF, kein Satz: die Bruecken von den
    einzelnen Beinen zu den Saetzen stehen nicht hier (Schnitt C6). -/
def satz_nachpruefung_vertrauen (eingabe : NachprueferEingabe) : Prop :=
  nachprueferGueltig eingabe →
    satz_korrespondenz eingabe.gabbroSites eingabe.cert ∧
    satz_alias eingabe.o ∧
    satz_kosten eingabe.k eingabe.paare absenkung eingabe.cAnweisungen

/-! ## 11. Die fuenf bepreisten Stellen: Preis als Datum, kein Bedeutungsanspruch -/

/-- Der Preis von `logUndOder` (`messung/CFORM-REGEL-LOGUNDODER.md`, 23 Stellen):
    bedingte Auswertung mit Sequenzpunkt, Ergebnis 0 oder 1, Klammerpflicht
    beim Erzeuger. Zulassung mit Preis, keine Erzeugeraenderung. -/
def logUndOderEntscheid : RulingStatus :=
  .aufListe "bedingte Auswertung mit Sequenzpunkt; Ergebnis 0 oder 1; Klammerpflicht beim Erzeuger"

/-- Der Preis von `fortStmt` (`messung/CFORM-REGEL-CONTINUE.md`, 3 Stellen):
    Steuerung des Laufenskeletts aus einer Emissionszeile, kein Nutzerpfad,
    kein UB. Zulassung mit Preis, keine Erzeugeraenderung. -/
def fortEntscheid : RulingStatus :=
  .aufListe "Steuerung des Laufenskeletts aus einer Emissionszeile; kein Nutzerpfad; kein UB"

/-- Der Preis von `abbruchStmt` (`messung/CFORM-REGEL-BREAK.md`, 51 Stellen):
    Austritt aus dem Laufenskelett und Abschluss der Fallarme aus je zwei
    Emissionszeilen, kein Nutzerpfad, kein UB. Zulassung mit Preis, keine
    Erzeugeraenderung. -/
def abbruchEntscheid : RulingStatus :=
  .aufListe "Austritt aus dem Laufenskelett und Abschluss der Fallarme aus je zwei Emissionszeilen; kein Nutzerpfad; kein UB"

/-- Der Preis von `zeigerIndex` (`messung/CFORM-REGEL-ZEIGERINDEX.md`,
    156 Stellen): Adressrechnung, Pflicht je Stelle, in den Grenzen zu bleiben,
    UB-Zeile fuer den Aussenfall. Zulassung mit Preis, keine
    Erzeugeraenderung. -/
def zeigerIndexEntscheid : RulingStatus :=
  .aufListe "Adressrechnung; Pflicht je Stelle, in den Grenzen zu bleiben; UB-Zeile fuer den Aussenfall"

/-- Die fuenf bepreisten Stellen als Nachtrag: `bedingt` traegt den gefuellten
    Musterentscheid, die vier Zulassungen ihre Preise aus den Regelnotizen.
    Jede andere Stelle faellt durch (`none`) und behaelt ihren alten Stand. -/
def tafelPreisNachtrag : OffeneForm → Option RulingStatus
  | .bedingt => some bedingtEntscheid
  | .logUndOder => some logUndOderEntscheid
  | .fortStmt => some fortEntscheid
  | .abbruchStmt => some abbruchEntscheid
  | .zeigerIndex => some zeigerIndexEntscheid
  | _ => none

/-- Der reine Statuswechsel: wo der Nachtrag einen Preis nennt, tritt er an die
    Stelle des alten Standes; sonst bleibt alles, wie es war. -/
def tafelStatusNeu (u : OffeneForm) (s : RulingStatus) : RulingStatus :=
  match tafelPreisNachtrag u with
  | some s' => s'
  | none => s

/-- Die Tafel mit den fuenf bepreisten Stellen: dieselben Zeilen wie `tafel`,
    nur das Statusfeld der fuenf Stellen entschieden mit Preis. `tafel` selbst
    bleibt eingefroren; diese Tafel traegt den Nachtrag als Datum, und die
    Angemessenheit jedes Preises bleibt geschuldet (Schnitt C7). -/
def tafelNeu : List EntscheidZiel :=
  tafel.map fun e => match e with
    | .benannt f s => .benannt f s
    | .luecke u s => .luecke u (tafelStatusNeu u s)

/-- Der spaetere Satz ueber der neuen Tafel, als Gestalt: jede Zeile von
    `tafelNeu` ist entschieden. ENTWURF, kein Satz -- wie `satz_tafel` eine
    SPEZIFIKATION bleibt, bis jede Stelle einzeln entschieden ist. -/
def satz_tafelNeu : Prop :=
  ∀ e ∈ tafelNeu, entschieden e

end Gabbro.Grammatik
